/// Conflict-Driven Clause Learning Search engine
use {
    super::{
        analyze::{analyze_final, conflict_analyze},
        restart::{RestartIF, Restarter, RestarterModule},
        Certificate, Solver, SolverResult,
    },
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarRewardIF, VarSelectIF},
        cdb::{ClauseDB, ClauseDBIF},
        processor::{EliminateIF, Eliminator},
        state::{PhaseMode, Stat, State, StateIF},
        types::*,
    },
    std::slice::Iter,
};

/// API for SAT solver like `build`, `solve` and so on.
pub trait SatSolverSearchIF {
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solve(&mut self) -> SolverResult;
}

macro_rules! final_report {
    ($asg: expr, $cdb: expr, $elim: expr, $rst: expr, $state: expr) => {
        let c = $state.config.no_color;
        let q = $state.config.quiet_mode;
        $state.config.no_color = true;
        $state.config.quiet_mode = false;
        if q {
            $state.progress_header();
        }
        $state.progress($asg, $cdb, $elim, $rst, None);
        $state.config.no_color = c;
        $state.config.quiet_mode = q;
    };
}

impl SatSolverSearchIF for Solver {
    /// # Examples
    ///
    /// ```
    /// use splr::config::Config;
    /// use splr::solver::{Certificate, SatSolverIF, Solver};
    ///
    /// let config = Config::from("tests/sample.cnf");
    /// if let Ok(mut s) = Solver::build(&config) {
    ///     let res = s.solve();
    ///     assert!(res.is_ok());
    ///     assert_ne!(res.unwrap(), Certificate::UNSAT);
    /// }
    ///```
    fn solve(&mut self) -> SolverResult {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut elim,
            ref mut rst,
            ref mut state,
        } = self;
        if cdb.check_size().is_err() {
            return Err(SolverError::OutOfMemory);
        }
        // NOTE: splr doesn't deal with assumptions.
        // s.root_level = 0;
        asg.num_solved_vars = asg.stack_len();
        state.progress_header();
        state.progress(asg, cdb, elim, rst, Some("preprocessing phase"));
        const USE_PRE_PROCESSING_ELIMINATOR: bool = true;

        //
        //## Propagate all trivial literals (an essential step)
        //
        // Set appropriate phases and push all the unit clauses to assign stack.
        // To do so, we use eliminator's ocuur list.
        // Thus we have to call `activate` and `prepare` firstly, to build occur lists.
        // Otherwise all literals are assigned wrongly.
        state.flush("phasing...");
        elim.activate();
        elim.prepare(asg, cdb, true);
        for vi in 1..=asg.num_vars {
            if asg.assign(vi).is_some() {
                continue;
            }
            match elim.stats(vi) {
                Some((_, 0)) => {
                    let l = Lit::from_assign(vi, true);
                    if asg.assign_at_rootlevel(l).is_err() {
                        return Ok(Certificate::UNSAT);
                    }
                }
                Some((0, _)) => {
                    let l = Lit::from_assign(vi, false);
                    if asg.assign_at_rootlevel(l).is_err() {
                        return Ok(Certificate::UNSAT);
                    }
                }
                Some((p, m)) => {
                    asg.var_mut(vi).set(Flag::PHASE, m < p);
                    elim.enqueue_var(asg, vi, false);
                }
                None => (),
            }
        }
        //
        //## Run eliminator
        //
        if !USE_PRE_PROCESSING_ELIMINATOR || !elim.enable {
            elim.stop(asg, cdb);
        }
        if USE_PRE_PROCESSING_ELIMINATOR && elim.enable {
            state.flush("simplifying...");
            // if 20_000_000 < state.target.num_of_clauses {
            //     state.elim_eliminate_grow_limit = 0;
            //     state.elim_eliminate_loop_limit = 1_000_000;
            //     state.elim_subsume_loop_limit = 2_000_000;
            // }
            if elim.simplify(asg, cdb, state).is_err() {
                // Why inconsistent? Because the CNF contains a conflict, not an error!
                // Or out of memory.
                final_report!(asg, cdb, elim, rst, state);
                if cdb.check_size().is_err() {
                    return Err(SolverError::OutOfMemory);
                }
                return Ok(Certificate::UNSAT);
            }
            for vi in 1..=asg.num_vars {
                if asg.assign(vi).is_some() || asg.var(vi).is(Flag::ELIMINATED) {
                    continue;
                }
                match elim.stats(vi) {
                    Some((_, 0)) => (),
                    Some((0, _)) => (),
                    Some((p, m)) if m * 10 < p => asg.var_mut(vi).turn_on(Flag::PHASE),
                    Some((p, m)) if p * 10 < m => asg.var_mut(vi).turn_off(Flag::PHASE),
                    _ => (),
                }
            }
            asg.initialize_reward(elim.sorted_iterator());
        }
        asg.rebuild_order();
        state.progress(asg, cdb, elim, rst, None);

        //
        //## Search
        //
        let answer = search(asg, cdb, elim, rst, state);
        final_report!(asg, cdb, elim, rst, state);
        match answer {
            Ok(true) => {
                asg.extend_model(elim.eliminated_lits());
                #[cfg(debug)]
                {
                    if let Some(cid) = cdb.validate(asg, true) {
                        panic!(
                            "Level {} generated assignment({:?}) falsifies {}:{:?}",
                            asg.decision_level(),
                            cdb.validate(asg, false).is_none(),
                            cid,
                            asg.dump(&cdb[cid]),
                        );
                    }
                }
                if cdb.validate(asg, false).is_some() {
                    return Err(SolverError::SolverBug);
                }
                let vals = asg
                    .var_iter()
                    .skip(1)
                    .map(|v| i32::from(Lit::from((v.index, asg.assign(v.index)))))
                    .collect::<Vec<i32>>();
                asg.cancel_until(asg.root_level);
                Ok(Certificate::SAT(vals))
            }
            Ok(false) | Err(SolverError::NullLearnt) => {
                asg.cancel_until(asg.root_level);
                Ok(Certificate::UNSAT)
            }
            Err(e) => {
                asg.cancel_until(asg.root_level);
                Err(e)
            }
        }
    }
}

/// main loop; returns `Ok(true)` for SAT, `Ok(false)` for UNSAT.
fn search(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
) -> Result<bool, SolverError> {
    let mut replay_best = false;
    let mut a_decision_was_made = false;
    let mut num_assigned = asg.num_solved_vars;
    rst.update(RestarterModule::Luby, 0);
    loop {
        asg.reward_update();
        let ci = asg.propagate(cdb);
        if ci == ClauseId::default() {
            if asg.num_vars <= asg.stack_len() + asg.num_eliminated_vars {
                return Ok(true);
            }

            //
            //## DYNAMIC FORCING RESTART based on LBD values, updated by conflict
            //
            state.last_asg = asg.stack_len();
            if rst.force_restart() {
                asg.cancel_until(asg.root_level);
            }
        } else {
            if asg.decision_level() == asg.root_level {
                analyze_final(asg, state, &cdb[ci]);
                return Ok(false);
            }
            if num_assigned < asg.stack_len() + asg.num_eliminated_vars {
                replay_best = false;
            }
            handle_conflict(asg, cdb, elim, rst, state, ci)?;
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state[Stat::NoDecisionConflict] += 1;
            }
        }
        // Simplification has been postponed because chronoBT was used.
        if asg.decision_level() == asg.root_level {
            replay_best = true;
            // `elim.to_eliminate` is increased much in particular when vars are solved or
            // learnts are small. We don't need to count the number of solved vars.
            if state.config.elim_trigger < elim.to_eliminate as usize {
                elim.to_eliminate = 0.0;
                if elim.enable {
                    elim.activate();
                }
                elim.simplify(asg, cdb, state)?;
            }
            // By simplification, we may get further solutions.
            if asg.num_solved_vars < asg.stack_len() {
                rst.update(RestarterModule::Reset, 0);
                asg.num_solved_vars = asg.stack_len();
            }
        }
        if !asg.remains() {
            //
            //## set phase mode
            //
            state.stabilize = state.config.stabilize && rst.stabilizing();
            let na = asg.best_assigned(Flag::BEST_PHASE);
            if num_assigned < na {
                num_assigned = na;
                // back_to_zero = false;
                state.flush("");
                state.flush(format!("unreachable: {}", asg.num_vars - num_assigned));
            }
            state.phase_select = if replay_best && state.stabilize {
                PhaseMode::Best
            } else {
                PhaseMode::Latest
            };
            let vi = asg.select_var();
            let p = match state.phase_select {
                PhaseMode::Best => asg.var(vi).is(Flag::BEST_PHASE),
                PhaseMode::BestRnd => match ((asg.activity(vi) * 10000.0) as usize) % 4 {
                    0 => asg.var(vi).is(Flag::BEST_PHASE),
                    _ => asg.var(vi).is(Flag::PHASE),
                },
                PhaseMode::Invert => !asg.var(vi).is(Flag::PHASE),
                PhaseMode::Latest => asg.var(vi).is(Flag::PHASE),
                PhaseMode::Random => ((asg.activity(vi) * 10000.0) as usize) % 2 == 0,
                PhaseMode::Target => asg.var(vi).is(Flag::TARGET_PHASE),
            };
            asg.assign_by_decision(Lit::from_assign(vi, p));
            state[Stat::Decision] += 1;
            a_decision_was_made = true;
        }
    }
}

#[allow(clippy::cognitive_complexity)]
fn handle_conflict(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    ci: ClauseId,
) -> MaybeInconsistent {
    let original_dl = asg.decision_level();
    // we need a catch here for handling the possibility of level zero conflict
    // at higher level due to the incoherence between the current level and conflicting
    // level in chronoBT. This leads to UNSAT solution. No need to update misc stats.
    {
        let level = asg.level_ref();
        if cdb[ci].iter().all(|l| level[l.vi()] == 0) {
            return Err(SolverError::NullLearnt);
        }
    }

    let (ncnfl, _num_propagation, asg_num_restart, _) = asg.exports();
    // If we can settle this conflict w/o restart, solver will get a big progress.
    let switch_chronobt = if ncnfl < 1000 || asg.recurrent_conflicts() {
        Some(false)
    } else {
        None
    };
    rst.update(RestarterModule::Counter, ncnfl);

    if 0 < state.last_asg {
        rst.update(RestarterModule::ASG, asg.stack_len());
        state.last_asg = 0;
    }

    //
    //## DYNAMIC BLOCKING RESTART based on ASG, updated on conflict path
    //
    rst.block_restart();
    let mut use_chronobt = switch_chronobt.unwrap_or(0 < state.config.cbt_thr);
    if use_chronobt {
        let level = asg.level_ref();
        let c = &cdb[ci];
        let lcnt = c.iter().filter(|l| level[l.vi()] == original_dl).count();
        if 1 == lcnt {
            debug_assert!(c.iter().any(|l| level[l.vi()] == original_dl));
            let decision = *c.iter().find(|l| level[l.vi()] == original_dl).unwrap();
            let snd_l = c
                .iter()
                .map(|l| level[l.vi()])
                .filter(|l| *l != original_dl)
                .max()
                .unwrap_or(0);
            if 0 < snd_l {
                // If the conflicting clause contains one literallfrom the maximal
                // decision level, we let BCP propagating that literal at the second
                // highest decision level in conflicting cls.
                // PREMISE: 0 < snd_l
                asg.cancel_until(snd_l - 1);
                debug_assert!(
                    asg.stack_iter().all(|l| l.vi() != decision.vi()),
                    format!("lcnt == 1: level {}, snd level {}", original_dl, snd_l)
                );
                asg.assign_by_decision(decision);
                return Ok(());
            }
        }
    }
    // conflicting level
    // By mixing two restart modes, we must assume a conflicting level is under the current decision level,
    // even if `use_chronobt` is off, because `use_chronobt` is a flag for future behavior.
    let cl = {
        let cl = asg.decision_level();
        let c = &cdb[ci];
        let level = asg.level_ref();
        let lv = c.iter().map(|l| level[l.vi()]).max().unwrap_or(0);
        if lv < cl {
            asg.cancel_until(lv);
            lv
        } else {
            cl
        }
    };
    debug_assert!(
        cdb[ci].iter().any(|l| asg.level(l.vi()) == cl),
        format!(
            "use_{}: {:?}, {:?}",
            use_chronobt,
            cl,
            cdb[ci]
                .iter()
                .map(|l| (i32::from(*l), asg.level(l.vi())))
                .collect::<Vec<_>>(),
        )
    );
    // backtrack level by analyze
    let bl_a = conflict_analyze(asg, cdb, state, ci).max(asg.root_level);
    if state.new_learnt.is_empty() {
        #[cfg(debug)]
        {
            println!(
                "empty learnt at {}({}) by {:?}",
                cl,
                asg.reason(asg.decision_vi(cl)) == ClauseId::default(),
                asg.dump(asg, &cdb[ci]),
            );
        }
        return Err(SolverError::NullLearnt);
    }
    // asg.bump_vars(asg, cdb, ci);
    let new_learnt = &mut state.new_learnt;
    let l0 = new_learnt[0];
    // assert: 0 < cl, which was checked already by new_learnt.is_empty().

    // NCB places firstUIP on level bl, while CB does it on level cl.
    // Therefore the condition to use CB is: activity(firstUIP) < activity(v(bl)).
    // PREMISE: 0 < bl, because asg.decision_vi accepts only non-zero values.
    use_chronobt &= switch_chronobt.unwrap_or(
        bl_a == 0
            || state.config.cbt_thr + bl_a <= cl
            || asg.activity(l0.vi()) < asg.activity(asg.decision_vi(bl_a)),
    );

    // (assign level, backtrack level)
    let (al, bl) = if use_chronobt {
        (
            {
                let level = asg.level_ref();
                new_learnt[1..]
                    .iter()
                    .map(|l| level[l.vi()])
                    .max()
                    .unwrap_or(0)
            },
            cl - 1,
        )
    } else {
        (bl_a, bl_a)
    };
    let learnt_len = new_learnt.len();
    if learnt_len == 1 {
        //
        //## PARTIAL FIXED SOLUTION by UNIT LEARNT CLAUSE GENERATION
        //
        // dump to certified even if it's a literal.
        cdb.certificate_add(new_learnt);
        if use_chronobt {
            asg.cancel_until(bl);
            debug_assert!(asg.stack_iter().all(|l| l.vi() != l0.vi()));
            asg.assign_by_implication(l0, AssignReason::default(), 0);
        } else {
            asg.assign_by_unitclause(l0);
        }
        asg.num_solved_vars += 1;
        rst.update(RestarterModule::Reset, 0);
        state.last_solved = ncnfl;
    } else {
        {
            // At the present time, some reason clauses can contain first UIP or its negation.
            // So we have to filter vars instead of literals to avoid double counting.
            let mut bumped = new_learnt.iter().map(|l| l.vi()).collect::<Vec<VarId>>();
            for lit in new_learnt.iter() {
                //
                //## Learnt Literal Rewarding
                //
                asg.reward_at_analysis(lit.vi());
                // if !state.stabilize {
                //     continue;
                // }
                if let AssignReason::Implication(r, _) = asg.reason(lit.vi()) {
                    for l in &cdb[r].lits {
                        let vi = l.vi();
                        if !bumped.contains(&vi) {
                            //
                            //## Reason-Side Rewarding
                            //
                            asg.reward_at_analysis(vi);
                            bumped.push(vi);
                        }
                    }
                }
            }
        }
        asg.cancel_until(bl);
        let cid = cdb.new_clause(asg, new_learnt, true, true);
        elim.add_cid_occur(asg, cid, &mut cdb[cid], true);
        state.c_lvl.update(cl as f64);
        state.b_lvl.update(bl as f64);
        asg.assign_by_implication(
            l0,
            AssignReason::Implication(
                cid,
                if learnt_len == 2 {
                    new_learnt[1]
                } else {
                    NULL_LIT
                },
            ),
            al,
        );
        let lbd = cdb[cid].rank;
        rst.update(RestarterModule::LBD, lbd);
        if 1 < learnt_len && learnt_len <= state.config.elim_cls_lim / 2 {
            elim.to_eliminate += 1.0 / (learnt_len - 1) as f64;
        }
    }
    cdb.scale_activity();
    if 0 < state.config.dump_int && ncnfl % state.config.dump_int == 0 {
        let (_mode, rst_num_block, rst_asg_trend, _lbd_get, rst_lbd_trend) = rst.exports();
        state.development.push((
            ncnfl,
            (asg.num_solved_vars + asg.num_eliminated_vars) as f64
                / state.target.num_of_variables as f64,
            asg_num_restart as f64,
            rst_num_block as f64,
            rst_asg_trend.min(10.0),
            rst_lbd_trend.min(10.0),
        ));
    }
    cdb.check_and_reduce(asg, ncnfl);
    if ncnfl % state.reflection_interval == 0 {
        adapt_modules(asg, cdb, elim, rst, state)?;
        if let Some(p) = state.elapsed() {
            if 1.0 <= p {
                return Err(SolverError::TimeOut);
            }
        } else {
            return Err(SolverError::UndescribedError);
        }
    }
    Ok(())
}

fn adapt_modules(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
) -> MaybeInconsistent {
    state.progress(asg, cdb, elim, rst, None);
    let (asg_num_conflict, _num_propagation, _num_restart, _) = asg.exports();
    if 10 * state.reflection_interval == asg_num_conflict {
        // Need to call it before `cdb.adapt_to`
        // 'decision_level == 0' is required by `cdb.adapt_to`.
        asg.cancel_until(asg.root_level);
        if elim.enable && elim.exports().0 < 3 {
            elim.activate();
            elim.simplify(asg, cdb, state)?;
        }
        state.select_strategy(asg, cdb);
        // if state.strategy.0 == SearchStrategy::HighSuccesive {
        //     state.config.cbt_thr = 0;
        // }
    }
    #[cfg(feature = "boundary_check")]
    assert!(state.strategy.1 != asg_num_conflict || 0 == asg.decision_level());
    asg.adapt_to(state, asg_num_conflict);
    cdb.adapt_to(state, asg_num_conflict);
    rst.adapt_to(state, asg_num_conflict);
    Ok(())
}

#[allow(dead_code)]
impl AssignStack {
    fn dump<'a, V: IntoIterator<Item = &'a Lit, IntoIter = Iter<'a, Lit>>>(
        &mut self,
        v: V,
    ) -> Vec<(i32, DecisionLevel, bool, Option<bool>)> {
        v.into_iter()
            .map(|l| {
                (
                    i32::from(l),
                    self.level(l.vi()),
                    self.reason(l.vi()) == AssignReason::default(),
                    self.assign(l.vi()),
                )
            })
            .collect::<Vec<(i32, DecisionLevel, bool, Option<bool>)>>()
    }
}

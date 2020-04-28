/// Conflict-Driven Clause Learning Search engine
use {
    super::{
        conflict::handle_conflict,
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
            if asg.exports().0 % state.reflection_interval == 0 {
                adapt_modules(asg, cdb, elim, rst, state)?;
                if let Some(p) = state.elapsed() {
                    if 1.0 <= p {
                        return Err(SolverError::TimeOut);
                    }
                } else {
                    return Err(SolverError::UndescribedError);
                }
            }
        }
        // Simplification has been postponed because chronoBT was used.
        if asg.decision_level() == asg.root_level {
            replay_best = true;
            // `elim.to_simplify` is increased much in particular when vars are solved or
            // learnts are small. We don't need to count the number of solved vars.
            if state.config.elim_trigger < elim.to_simplify as usize {
                elim.to_simplify = 0.0;
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
        if elim.enable && elim.exports().0 < 2 {
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

fn analyze_final(asg: &mut AssignStack, state: &mut State, c: &Clause) {
    let mut seen = vec![false; asg.num_vars + 1];
    state.conflicts.clear();
    if asg.decision_level() == 0 {
        return;
    }
    for l in &c.lits {
        let vi = l.vi();
        if 0 < asg.level(vi) {
            asg.var_mut(vi).turn_on(Flag::CA_SEEN);
        }
    }
    let end = if asg.decision_level() <= asg.root_level {
        asg.stack_len()
    } else {
        asg.len_upto(asg.root_level)
    };
    for l in asg.stack_range(asg.len_upto(0)..end) {
        let vi = l.vi();
        if seen[vi] {
            if asg.reason(vi) == AssignReason::default() {
                state.conflicts.push(!*l);
            } else {
                let level = asg.level_ref();
                for l in &c[(c.len() != 2) as usize..] {
                    let vj = l.vi();
                    if 0 < level[vj] {
                        seen[vj] = true;
                    }
                }
            }
        }
        seen[vi] = false;
    }
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

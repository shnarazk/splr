//! Conflict-Driven Clause Learning Search engine
#[cfg(feature = "staging")]
use crate::state::StagingTarget;
use {
    super::{
        conflict::handle_conflict,
        restart::{ProgressUpdate, RestartDecision, RestartIF, Restarter},
        vivify::vivify,
        Certificate, Solver, SolverEvent, SolverResult,
    },
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarSelectIF},
        cdb::{ClauseDB, ClauseDBIF},
        processor::{EliminateIF, Eliminator},
        state::{Stat, State, StateIF},
        types::*,
    },
};

/// API to [`solve`](`crate::solver::SolveIF::solve`) SAT problems.
pub trait SolveIF {
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solve(&mut self) -> SolverResult;
}

macro_rules! RESTART {
    ($asg: expr, $rst: expr) => {
        $asg.cancel_until($asg.root_level);
        $rst.handle(SolverEvent::Restart);
    };
}

impl SolveIF for Solver {
    /// # Examples
    ///
    /// ```
    /// use splr::*;
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
        asg.num_asserted_vars = asg.stack_len();
        state.progress_header();
        state.progress(asg, cdb, elim, rst);
        state.flush("");
        state.flush("Preprocessing stage: ");
        if 0 < asg.stack_len() {
            elim.eliminate_satisfied_clauses(asg, cdb, false);
        }
        if elim.enable {
            const USE_PRE_PROCESSING_ELIMINATOR: bool = true;

            //
            //## Propagate all trivial literals (an essential step)
            //
            // Set appropriate phases and push all the unit clauses to assign stack.
            // To do so, we use eliminator's occur list.
            // Thus we have to call `activate` and `prepare` firstly, to build occur lists.
            // Otherwise all literals are assigned wrongly.
            state.flush("phasing...");
            elim.activate();
            elim.prepare(asg, cdb, true);
            for vi in 1..=asg.num_vars {
                if asg.assign(vi).is_some() {
                    continue;
                }
                if let Some((p, m)) = elim.stats(vi) {
                    // We can't call `asg.assign_at_root_level(l)` even if p or m == 0.
                    // This means we can't pick `!l`.
                    // This becomes a problem in the case of incremental solving.
                    #[cfg(not(feature = "incremental_solver"))]
                    {
                        if m == 0 {
                            let l = Lit::from_assign(vi, true);
                            if asg.assign_at_root_level(l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        } else if p == 0 {
                            let l = Lit::from_assign(vi, false);
                            if asg.assign_at_root_level(l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        }
                    }
                    asg.var_mut(vi).set(Flag::PHASE, m < p);
                    elim.enqueue_var(asg, vi, false);
                }
            }
            //
            //## Run eliminator
            //
            if USE_PRE_PROCESSING_ELIMINATOR {
                state.flush("simplifying...");
                if elim.simplify(asg, cdb, state).is_err() {
                    // Why inconsistent? Because the CNF contains a conflict, not an error!
                    // Or out of memory.
                    state.progress(asg, cdb, elim, rst);
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
                for vi in elim.sorted_iterator() {
                    asg.initialize_reward(*vi);
                }
                asg.rebuild_order();
            }
            elim.stop(asg, cdb);
        }

        //
        //## Search
        //
        state.progress(asg, cdb, elim, rst);
        let answer = search(asg, cdb, elim, rst, state);
        state.progress(asg, cdb, elim, rst);
        match answer {
            Ok(true) => {
                // As a preparation for incremental solving, we need to backtrack to the
                // root level. So all assignments, including assignments to eliminated vars,
                // are stored in an extra storage. It has the same type of `AssignStack::assign`.
                let model = asg.extend_model(cdb, elim.eliminated_lits());
                #[cfg(debug)]
                {
                    if let Some(cid) = cdb.validate(&model, true) {
                        panic!(
                            "Level {} generated assignment({:?}) falsifies {}:{:?}",
                            asg.decision_level(),
                            cdb.validate(&model, false).is_none(),
                            cid,
                            "asg.dump(&cdb[cid])",
                        );
                    }
                }

                // Run validator on the extended model.
                if cdb.validate(&model, false).is_some() {
                    return Err(SolverError::SolverBug);
                }

                // map `Option<bool>` to `i32`, and remove the dummy var at the head.
                let vals = asg
                    .var_iter()
                    .skip(1)
                    .map(|v| i32::from(Lit::from((v.index, model[v.index]))))
                    .collect::<Vec<i32>>();

                // As a preparation for incremental solving, turn flags off.
                for v in asg.var_iter_mut().skip(1) {
                    if v.is(Flag::ELIMINATED) {
                        v.turn_off(Flag::ELIMINATED);
                    }
                }
                RESTART!(asg, rst);
                Ok(Certificate::SAT(vals))
            }
            Ok(false) | Err(SolverError::NullLearnt) => {
                RESTART!(asg, rst);
                Ok(Certificate::UNSAT)
            }
            Err(e) => {
                RESTART!(asg, rst);
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
    let mut a_decision_was_made = false;
    let use_vivify = state.config.use_vivify();
    let mut parity = false;
    let mut last_core = 0;
    rst.update(ProgressUpdate::Luby);
    rst.update(ProgressUpdate::Remain(asg.num_vars - asg.num_asserted_vars));

    loop {
        let ci = asg.propagate(cdb);
        if ci.is_none() {
            //
            //## NO CONFLICT PATH
            //
            state.last_asg = state.last_asg.max(asg.stack_len());
            if asg.num_vars <= state.last_asg + asg.num_eliminated_vars {
                return Ok(true);
            }
        } else {
            //
            //## CONFLICT
            //
            if 0 < state.last_asg {
                rst.update(ProgressUpdate::ASG(state.last_asg));
                state.last_asg = 0;
            }
            if asg.decision_level() == asg.root_level {
                analyze_final(asg, state, &cdb[ci]);
                return Ok(false);
            }
            cdb.update_rewards();
            handle_conflict(asg, cdb, elim, rst, state, ci)?;
            asg.update_rewards();
            rst.update(ProgressUpdate::Remain(asg.var_stats().3));
            if let Some(decision) = rst.restart() {
                if let Some(new_cycle) = rst.stabilize() {
                    RESTART!(asg, rst);
                    let r = rst.exports();
                    if new_cycle {
                        let v = asg.var_stats();
                        let s = {
                            #[cfg(not(feature = "staging"))]
                            {
                                0
                            }
                            #[cfg(feature = "staging")]
                            {
                                asg.num_staging_cands()
                            }
                        };
                        parity = !parity;

                        #[cfg(feature = "staging")]
                        {
                            let d = 1.0 / ((s + 2) as f64).log(2.0);
                            rst.update(ProgressUpdate::Temperature(d));
                            asg.build_stage(StagingTarget::AutoSelect, parity);
                        }

                        if last_core != v.4 || 0 == v.4 {
                            state.log(
                                asg.num_conflict,
                                format!(
                                    "Lcycle:{:>6}, core:{:>9}, #ion: {:>9}, /cpr:{:>9.2}",
                                    r.3,
                                    v.4,
                                    s,
                                    asg.exports_box().2.get(),
                                ),
                            );
                            last_core = v.4;
                        }
                    } else {
                        #[cfg(feature = "staging")]
                        {
                            asg.dissolve_stage(parity);
                        }
                    }

                    if cdb.reduce(asg, asg.num_conflict) {
                        state.to_vivify += 1.0;
                    } else {
                        state.to_vivify += 0.1;
                    }
                    if use_vivify && 1.0 <= state.to_vivify {
                        if vivify(asg, cdb, elim, state).is_err() {
                            // return Err(SolverError::UndescribedError);
                            analyze_final(asg, state, &cdb[ci]);
                            return Ok(false);
                        }
                        state.to_vivify = 0.0;
                    }
                    // Simplification has been postponed because chronoBT was used.
                    // `elim.to_simplify` is increased much in particular
                    // when vars are asserted or learnts are small.
                    // We don't need to count the number of asserted vars.
                    if elim.enable && state.config.c_ip_int <= elim.to_simplify as usize {
                        elim.to_simplify = 0.0;

                        #[cfg(feature = "progress_MLD")]
                        {
                            elim.subsume_literal_limit = (rst.mld.get_slow() * 2.0) as usize;
                        }

                        elim.activate();
                        elim.simplify(asg, cdb, state)?;
                    }
                } else if RestartDecision::Force == decision {
                    RESTART!(asg, rst);
                }
            }
            // By simplification, we may get further solutions.
            if asg.decision_level() == asg.root_level && asg.num_asserted_vars < asg.stack_len() {
                asg.num_asserted_vars = asg.stack_len();
            }
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state[Stat::NoDecisionConflict] += 1;
            }
            if let Some(na) = asg.best_assigned() {
                state.flush("");
                state.flush(format!("unreachable core: {}", na));
            }
            if asg.num_conflict % state.reflection_interval == 0 {
                adapt_modules(asg, cdb, elim, rst, state);
                if let Some(p) = state.elapsed() {
                    if 1.0 <= p {
                        return Err(SolverError::TimeOut);
                    }
                } else {
                    return Err(SolverError::UndescribedError);
                }
            }
        }
        if !asg.remains() {
            let lit = asg.select_decision_literal();
            asg.assign_by_decision(lit);
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
) {
    state.progress(asg, cdb, elim, rst);
    let asg_num_conflict = asg.num_conflict;
    if 10 * state.reflection_interval == asg_num_conflict {
        // Need to call it before `cdb.adapt_to`
        // 'decision_level == 0' is required by `cdb.adapt_to`.
        RESTART!(asg, rst);

        #[cfg(feature = "strategy_adaptation")]
        {
            state.select_strategy(asg, cdb);
        }
    }
    #[cfg(feature = "strategy_adaptation")]
    {
        #[cfg(feature = "boundary_check")]
        debug_assert!(state.strategy.1 != asg_num_conflict || 0 == asg.decision_level());

        asg.handle(SolverEvent::Adapt(state.strategy, asg_num_conflict));
        cdb.handle(SolverEvent::Adapt(state.strategy, asg_num_conflict));
        rst.handle(SolverEvent::Adapt(state.strategy, asg_num_conflict));
    }
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

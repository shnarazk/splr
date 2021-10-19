//! Conflict-Driven Clause Learning Search engine
#[cfg(feature = "clause_vivification")]
use super::vivify::vivify;
use {
    super::{
        conflict::handle_conflict,
        restart::{self, ProgressUpdate, RestartDecision, RestartIF, Restarter},
        Certificate, Solver, SolverEvent, SolverResult,
    },
    crate::{
        assign::{self, AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarSelectIF},
        cdb::{self, ClauseDB, ClauseDBIF},
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
        $asg.cancel_until($asg.root_level());
        $rst.handle(SolverEvent::Restart);
    };
}

impl SolveIF for Solver {
    /// # Examples
    ///
    /// ```
    /// use splr::*;
    ///
    /// let config = Config::from("cnfs/sample.cnf");
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
        state.progress_header();
        state.progress(asg, cdb, elim, rst);
        state.flush("");
        state.flush("Preprocessing stage: ");

        state[Stat::NumProcessor] += 1;
        #[cfg(feature = "clause_vivification")]
        {
            state.flush("vivifying...");
            if vivify(asg, cdb, rst, state).is_err() {
                #[cfg(feature = "support_user_assumption")]
                {
                    analyze_final(asg, state, &cdb[ci]);
                }
                state.log(asg.num_conflict, "By vivifier as a pre-possessor");
                return Ok(Certificate::UNSAT);
            }
            assert!(!asg.remains());
        }
        debug_assert_eq!(asg.decision_level(), asg.root_level());
        if elim.simplify(asg, cdb, rst, state).is_err() {
            if cdb.check_size().is_err() {
                return Err(SolverError::OutOfMemory);
            }
            state.log(asg.num_conflict, "By eliminator");
            return Ok(Certificate::UNSAT);
        }

        #[cfg(feature = "clause_elimination")]
        {
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
                            let l = Lit::from((vi, true));
                            assert!(asg.assigned(l).is_none());
                            cdb.certificate_add_assertion(l);
                            if asg.assign_at_root_level(l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        } else if p == 0 {
                            let l = Lit::from((vi, false));
                            assert!(asg.assigned(l).is_none());
                            cdb.certificate_add_assertion(l);
                            if asg.assign_at_root_level(l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        }
                    }
                    asg.var_mut(vi).set(FlagVar::PHASE, m < p);
                    elim.enqueue_var(asg, vi, false);
                }
            }
            //
            //## Run eliminator
            //
            if USE_PRE_PROCESSING_ELIMINATOR {
                state.flush("simplifying...");
                if elim.simplify(asg, cdb, rst, state).is_err() {
                    // Why inconsistent? Because the CNF contains a conflict, not an error!
                    // Or out of memory.
                    state.progress(asg, cdb, elim, rst);
                    if cdb.check_size().is_err() {
                        return Err(SolverError::OutOfMemory);
                    }
                    return Ok(Certificate::UNSAT);
                }
                for vi in 1..=asg.num_vars {
                    if asg.assign(vi).is_some() || asg.var(vi).is(FlagVar::ELIMINATED) {
                        continue;
                    }
                    match elim.stats(vi) {
                        Some((_, 0)) => (),
                        Some((0, _)) => (),
                        Some((p, m)) if m * 10 < p => asg.var_mut(vi).turn_on(FlagVar::PHASE),
                        Some((p, m)) if p * 10 < m => asg.var_mut(vi).turn_off(FlagVar::PHASE),
                        _ => (),
                    }
                }
                let act = 1.0 / (asg.num_vars as f64).powf(0.25);
                for vi in 1..asg.num_vars {
                    if !asg.var(vi).is(FlagVar::ELIMINATED) {
                        asg.set_activity(vi, act);
                    }
                }
                asg.rebuild_order();
            }
        }

        //
        //## Search
        //
        state.progress(asg, cdb, elim, rst);
        let answer = search(asg, cdb, elim, rst, state);
        state.progress(asg, cdb, elim, rst);
        match answer {
            Ok(true) => {
                #[cfg(feature = "trace_equivalency")]
                {
                    asg.dump_cnf(cdb, "last-step.cnf");
                }
                // As a preparation for incremental solving, we need to backtrack to the
                // root level. So all assignments, including assignments to eliminated vars,
                // are stored in an extra storage. It has the same type of `AssignStack::assign`.
                #[cfg(feature = "boundary_check")]
                check(asg, cdb, true, "Before extending the model");

                #[cfg(fueature = "boundary_check")]
                check(asg, cdb, true, "Before extending the model");

                let model = asg.extend_model(cdb, elim.eliminated_lits());

                #[cfg(fueature = "boundary_check")]
                check(
                    asg,
                    cdb,
                    true,
                    "After extending the model, (passed before extending)",
                );

                // Run validator on the extended model.
                if cdb.validate(&model, false).is_some() {
                    state.log(asg.num_conflict, "failed to validate the extended model");
                    state.progress(asg, cdb, elim, rst);
                    return Err(SolverError::SolverBug);
                }

                // map `Option<bool>` to `i32`, and remove the dummy var at the head.
                let vals = asg
                    .var_iter()
                    .enumerate()
                    .skip(1)
                    .map(|(vi, _)| i32::from(Lit::from((vi, model[vi]))))
                    .collect::<Vec<i32>>();

                // As a preparation for incremental solving, turn flags off.
                for v in asg.var_iter_mut().skip(1) {
                    if v.is(FlagVar::ELIMINATED) {
                        v.turn_off(FlagVar::ELIMINATED);
                    }
                }
                RESTART!(asg, rst);
                Ok(Certificate::SAT(vals))
            }
            Ok(false) | Err(SolverError::EmptyClause | SolverError::RootLevelConflict(_)) => {
                #[cfg(feature = "support_user_assumption")]
                {
                    analyze_final(asg, state, &cdb[ci]);
                }
                RESTART!(asg, rst);
                Ok(Certificate::UNSAT)
            }
            Err(e) => {
                RESTART!(asg, rst);
                state.progress(asg, cdb, elim, rst);
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
    #[cfg(feature = "strategy_adaptation")]
    let mut a_decision_was_made = false;

    #[cfg(feature = "Luby_restart")]
    rst.update(ProgressUpdate::Luby);

    while 0 < asg.derefer(assign::property::Tusize::NumUnassignedVar) || asg.remains() {
        if !asg.remains() {
            let lit = asg.select_decision_literal();
            asg.assign_by_decision(lit);

            #[cfg(feature = "strategy_adaptation")]
            {
                a_decision_was_made = true;
            }
        }
        if let Err(cc) = asg.propagate(cdb) {
            if asg.decision_level() == asg.root_level() {
                return Err(SolverError::RootLevelConflict(cc));
            }

            #[cfg(feature = "strategy_adaptation")]
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state[Stat::NoDecisionConflict] += 1;
            }

            asg.update_activity_tick();
            cdb.update_activity_tick();
            handle_conflict(asg, cdb, rst, state, &cc)?;
            rst.update(ProgressUpdate::ASG(
                asg.derefer(assign::property::Tusize::NumUnassignedVar),
            ));
            if cdb.should_reduce(asg.num_conflict) {
                if let Some(p) = state.elapsed() {
                    if 1.0 <= p {
                        return Err(SolverError::TimeOut);
                    }
                } else {
                    return Err(SolverError::UndescribedError);
                }
                RESTART!(asg, rst);
                cdb.reduce(asg, asg.num_conflict);

                #[cfg(feature = "trace_equivalency")]
                cdb.check_consistency(asg, "before simplify");

                #[cfg(feature = "clause_vivification")]
                vivify(asg, cdb, rst, state)?;

                #[cfg(feature = "clause_elimination")]
                {
                    elim.activate();
                    elim.simplify(asg, cdb, rst, state)?;
                    state[Stat::NumProcessor] += 1;
                }

                asg.clear_asserted_literals(cdb)?;
                // display the current stats. before updating stabiliation parameters
                state.log(
                    asg.num_conflict,
                    format!(
                        "core:{:>9}, cpr:{:>9.2}, scale:{:>4}, rlt:{:>7.4}",
                        asg.derefer(assign::property::Tusize::NumUnreachableVar),
                        asg.refer(assign::property::TEma::PropagationPerConflict)
                            .get(),
                        rst.derefer(restart::property::Tusize::IntervalScale),
                        rst.derefer(restart::property::Tf64::RestartThreshold),
                    ),
                );
                state.progress(asg, cdb, elim, rst);

                #[cfg(feature = "Luby_stabilization")]
                {
                    #[cfg(feature = "dynamic_restart_threshold")]
                    if 1 == rst.derefer(restart::property::Tusize::IntervalScale) {
                        rst.adjust(
                            state.config.rst_lbd_thr,
                            state.c_lvl.get(),
                            state.b_lvl.get(),
                            cdb.derefer(cdb::property::Tf64::DpAverageLBD),
                        );
                    }

                    rst.stabilize();
                    // call the enhanced phase saver
                    asg.handle(SolverEvent::Stabilize(
                        rst.derefer(restart::property::Tusize::IntervalScale),
                    ));
                }
            } else if rst.restart() == Some(RestartDecision::Force) {
                RESTART!(asg, rst);
            }
            if let Some(na) = asg.best_assigned() {
                state.flush("");
                state.flush(format!("unreachable core: {}", na));
            }
            #[cfg(feature = "strategy_adaptation")]
            if asg.num_conflict % (10 * state.reflection_interval) == 0 {
                adapt_modules(asg, cdb, rst, state);
            }
        }
    }
    state.log(
        asg.num_conflict,
        format!(
            "search process finished at level {}:: {} = {} - {} - {}",
            asg.decision_level(),
            asg.derefer(assign::property::Tusize::NumUnassignedVar),
            asg.num_vars,
            asg.num_eliminated_vars,
            asg.stack_len(),
        ),
    );
    Ok(true)
}

#[cfg(feature = "boundary_check")]
#[allow(dead_code)]
fn check(asg: &mut AssignStack, cdb: &mut ClauseDB, all: bool, message: &str) {
    if let Some(cid) = cdb.validate(asg.assign_ref(), all) {
        println!("{}", message);
        println!(
            "falsifies by {} at level {}, NumConf {}",
            cid,
            asg.decision_level(),
            asg.derefer(assign::property::Tusize::NumConflict),
        );
        assert!(asg.stack_iter().all(|l| asg.assigned(*l) == Some(true)));
        let (c0, c1) = cdb.watch_caches(cid, "check (search 441)");
        println!(
            " which was born at {}, and used in conflict analysis at {}",
            cdb[cid].birth,
            cdb[cid].timestamp(),
        );
        println!(
            " which was moved among watch caches at {:?}",
            cdb[cid].moved_at
        );
        println!("Its literals: {}", &cdb[cid]);
        println!(" |   pos |   time | level |   literal  |  assignment |               reason |");
        let l0 = i32::from(cdb[cid].lit0());
        let l1 = i32::from(cdb[cid].lit1());
        use crate::assign::DebugReportIF;

        for assign::Assign {
            lit,
            val,
            pos,
            lvl,
            by: reason,
            at,
            state,
        } in cdb[cid].report(asg).iter()
        {
            println!(
                " |{:>6} | {:>6} |{:>6} | {:9}{} | {:11} | {:20} | {:?}",
                pos.unwrap_or(0),
                at,
                lvl,
                lit,
                if *lit == l0 || *lit == l1 { '*' } else { ' ' },
                format!("{:?}", val),
                format!("{}", reason),
                state,
            );
        }
        println!(
            " - L0 {} has complements {:?} in its cache",
            cdb[cid].lit0(),
            c0
        );
        println!(
            " - L1 {} has complements {:?} in its cache",
            cdb[cid].lit1(),
            c1
        );
        println!("The last assigned literal in stack:");
        let last_lit = asg.stack(asg.stack_len() - 1);
        println!(
            " |{:>6} | {:>6} |{:>6} | {:9}  | {:11} | {:20} |",
            asg.stack_len() - 1,
            asg.var(last_lit.vi()).propagated_at,
            asg.level(last_lit.vi()),
            i32::from(last_lit),
            format!("{:?}", asg.assigned(last_lit),),
            format!("{}", asg.reason(last_lit.vi())),
        );
        panic!();
    }
}

#[cfg(feature = "strategy_adaptation")]
fn adapt_modules(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    rst: &mut Restarter,
    state: &mut State,
) {
    let asg_num_conflict = asg.num_conflict;
    if 10 * state.reflection_interval == asg_num_conflict {
        // Need to call it before `cdb.adapt_to`
        // 'decision_level == 0' is required by `cdb.adapt_to`.
        RESTART!(asg, rst);
        state.select_strategy(asg, cdb);
    }
    #[cfg(feature = "boundary_check")]
    debug_assert!(state.strategy.1 != asg_num_conflict || 0 == asg.decision_level());

    asg.handle(SolverEvent::Adapt(state.strategy, asg_num_conflict));
    cdb.handle(SolverEvent::Adapt(state.strategy, asg_num_conflict));
    rst.handle(SolverEvent::Adapt(state.strategy, asg_num_conflict));
}

#[cfg(feature = "support_user_assumption")]
// Build a conflict clause caused by *assumed* literals UNDER ROOT_LEVEL.
// So we use zero instead of root_level sometimes in this function.
fn analyze_final(asg: &mut AssignStack, state: &mut State, c: &Clause) {
    let mut seen = vec![false; asg.num_vars + 1];
    state.conflicts.clear();
    if asg.decision_level() == 0 {
        return;
    }
    // ??
    // for l in &c.lits {
    //     let vi = l.vi();
    //     if asg.root_level < asg.level(vi) {
    //         asg.var_mut(vi).turn_on(Flag::CA_SEEN);
    //     }
    // }
    // FIXME: asg.stack_range().rev() is correct.
    for l in asg.stack_range(0..asg.len_upto(asg.root_level)) {
        let vi = l.vi();
        if seen[vi] {
            if let AssignReason::Decision(_) = asg.reason(vi) {
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

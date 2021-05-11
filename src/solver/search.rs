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
        if 0 < asg.stack_len() {
            elim.eliminate_satisfied_clauses(asg, cdb, false);
        }

        state[Stat::NumProcessor] += 1;
        #[cfg(feture = "clause_vivification")]
        {
            state.flush("vivifying...");
            if vivify(asg, cdb, rst, state).is_err() {
                #[cfg(feature = "support_user_assumption")]
                {
                    analyze_final(asg, state, &cdb[ci]);
                }
                state.log(asg.num_conflict, "By vivifier as a prepossessor");
                return Ok(Certificate::UNSAT);
            }
            assert!(!asg.remains());
        }
        assert_eq!(asg.decision_level(), asg.root_level);
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
                            if asg.assign_at_root_level(l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        } else if p == 0 {
                            let l = Lit::from((vi, false));
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
                let act = 1.0 / (asg.num_vars as f64).powf(0.25);
                for vi in elim.sorted_iterator() {
                    if !asg.var(*vi).is(Flag::ELIMINATED) {
                        asg.set_activity(*vi, act);
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
                    asg.dump_cnf(cdb, "laststep.cnf");
                }
                // As a preparation for incremental solving, we need to backtrack to the
                // root level. So all assignments, including assignments to eliminated vars,
                // are stored in an extra storage. It has the same type of `AssignStack::assign`.
                // check(asg, cdb, false, "before");
                let model = asg.extend_model(cdb, elim.eliminated_lits());
                check(asg, cdb, true, "after extending the model");

                // Run validator on the extended model.
                if cdb.validate(&model, false).is_some() {
                    state.log(asg.num_conflict, "failed to validade the extended model");
                    state.progress(asg, cdb, elim, rst);
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
    let mut a_decision_was_made = false;
    let mut last_core = 0;
    let progress_step = 256;
    let mut next_progress = progress_step;

    #[cfg(feature = "Luby_restart")]
    rst.update(ProgressUpdate::Luby);

    while 0 < asg.derefer(assign::property::Tusize::NumUnassignedVar) || asg.remains() {
        if !asg.remains() {
            let lit = asg.select_decision_literal();
            asg.assign_by_decision(lit);
            a_decision_was_made = true;
        }
        let ci = asg.propagate(cdb);
        if !ci.is_none() {
            if asg.decision_level() == asg.root_level {
                #[cfg(feature = "support_user_assumption")]
                {
                    analyze_final(asg, state, &cdb[ci]);
                }
                return Ok(false);
            }
            asg.update_rewards();
            cdb.update_rewards();
            if let Err(e) = handle_conflict(asg, cdb, elim, rst, state, ci) {
                match e {
                    SolverError::RootLevelConflict(_) => return Ok(false),
                    _ => return Err(e),
                }
            }
            rst.update(ProgressUpdate::ASG(
                asg.derefer(assign::property::Tusize::NumUnassignedVar),
            ));
            if rst.restart() == Some(RestartDecision::Force) {
                #[allow(unused_variables)]
                if let Some(new_cycle) = rst.stabilize() {
                    RESTART!(asg, rst);
                    let block_level = rst.derefer(restart::property::Tusize::TriggerLevel);
                    let num_cycle = rst.derefer(restart::property::Tusize::NumCycle);
                    let num_unreachable = asg.derefer(assign::property::Tusize::NumUnreachableVar);
                    #[cfg(feature = "trace_equivalency")]
                    {
                        let num_stage = rst.derefer(restart::property::Tusize::NumStage);
                        if new_cycle {
                            asg.dump_cnf(
                                cdb,
                                &format!(
                                    "{}-stage{}.cnf",
                                    state.config.cnf_file.file_stem().unwrap().to_string_lossy(),
                                    num_stage
                                ),
                            );
                        }
                    }
                    asg.handle(SolverEvent::NewStabilizationStage(block_level));
                    // check(asg, cdb, false, "before reduction");
                    assert_eq!(asg.root_level, asg.decision_level());
                    if cdb.reduce(asg, asg.num_conflict) {
                        #[cfg(feature = "trace_equivalency")]
                        if false {
                            state.progress(asg, cdb, elim, rst);
                            cdb.check_consistency(asg, "before simplify");
                        }
                        state[Stat::NumProcessor] += 1;
                        if state.config.c_ip_int <= elim.to_simplify as usize {
                            assert_eq!(asg.root_level, asg.decision_level());
                            #[cfg(feature = "clause_vivification")]
                            if let Err(e) = vivify(asg, cdb, rst, state).and_then(|_| {
                                elim.activate();
                                elim.simplify(asg, cdb, rst, state)
                            }) {
                                match e {
                                    SolverError::RootLevelConflict(_) => {
                                        #[cfg(feature = "support_user_assumption")]
                                        {
                                            analyze_final(asg, state, &cdb[ci]);
                                        }
                                        state.log(asg.num_conflict, "at the in-processor");
                                        return Ok(false);
                                    }
                                    _ => return Err(e),
                                }
                            }
                            // check(asg, cdb, false, "after elimination");
                            #[cfg(feature = "trace_equivalency")]
                            if false {
                                state.progress(asg, cdb, elim, rst);
                                cdb.check_consistency(
                                    asg,
                                    &format!("simplify nc:{}", asg.num_conflict),
                                );
                            }
                        }
                    }
                    if last_core != num_unreachable || 0 == num_unreachable {
                        state.log(
                            asg.num_conflict,
                            format!(
                                "#cycle:{:>5}, core:{:>10}, level:{:>9}, /cpr:{:>9.2}",
                                num_cycle,
                                num_unreachable,
                                block_level,
                                asg.refer(assign::property::TEma::PropagationPerConflict)
                                    .get(),
                            ),
                        );
                        last_core = num_unreachable;
                    } else if let Some(p) = state.elapsed() {
                        if 1.0 <= p {
                            return Err(SolverError::TimeOut);
                        }
                    } else {
                        return Err(SolverError::UndescribedError);
                    }
                    if next_progress < asg.num_conflict {
                        state.progress(asg, cdb, elim, rst);
                        next_progress = asg.num_conflict + progress_step;
                    }
                } else {
                    RESTART!(asg, rst);
                }
            }
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state[Stat::NumDecisionConflict] += 1;
            }
            if let Some(na) = asg.best_assigned() {
                state.flush("");
                state.flush(format!("unreachable core: {}", na));
            }
            #[cfg(feature = "strategy_adaptation")]
            if asg.num_conflict % (10 * state.reflection_interval) == 0 {
                adapt_modules(asg, rst, state);
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

#[allow(dead_code)]
fn check(asg: &mut AssignStack, cdb: &mut ClauseDB, all: bool, message: &str) {
    if let Some(cid) = cdb.validate(asg.assign_ref(), all) {
        println!("{}", message);
        println!("| timestamp | level |   literal  |  assignment  |                  reason  |");
        let l0 = i32::from(cdb[cid].lit0());
        let l1 = i32::from(cdb[cid].lit1());
        for (t, lv, lit, reason, assign) in asg.dump(&cdb[cid]).iter() {
            println!(
                "|{:>10} |{:>6} | {:9}{} | {:12} | {:24} |",
                t,
                lv,
                lit,
                if *lit == l0 || *lit == l1 { '*' } else { ' ' },
                format!(
                    "{:?}{}",
                    assign,
                    if asg.var(lit.abs() as usize).is(Flag::PROPAGATED) {
                        "x"
                    } else {
                        "!"
                    },
                ),
                format!("{}", reason),
            );
        }
        println!("clause detail: {}", &cdb[cid]);
        let (w0, w1) = cdb.watches(cid, "search354");
        println!("watch{} has blocker{}", cdb[cid].lit0(), w0,);
        println!("watch{} has blocker{}", cdb[cid].lit1(), w1,);
        panic!(
            "Before extending, NC {}, Level {} generated assignment({:?}) falsifies by {}",
            asg.derefer(assign::property::Tusize::NumConflict),
            asg.decision_level(),
            cdb.validate(asg.assign_ref(), false).is_none(),
            cid,
        );
    }
}

#[cfg(feature = "strategy_adaptation")]
fn adapt_modules(asg: &mut AssignStack, rst: &mut Restarter, state: &mut State) {
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

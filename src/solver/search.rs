//! Conflict-Driven Clause Learning Search engine
use {
    super::{
        conflict::handle_conflict,
        restart::{self, RestartDecision, RestartIF, Restarter},
        Certificate, Solver, SolverEvent, SolverResult,
    },
    crate::{
        assign::{self, AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarSelectIF},
        cdb::{self, ClauseDB, ClauseDBIF, VivifyIF},
        processor::{EliminateIF, Eliminator},
        state::{State, StateIF},
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

        #[cfg(feature = "clause_vivification")]
        {
            state.flush("vivifying...");
            if cdb.vivify(asg, rst, state).is_err() {
                #[cfg(feature = "support_user_assumption")]
                analyze_final(asg, state, &cdb[ci]);

                state.log(asg.num_conflict, "By vivifier as a pre-possessor");
                return Ok(Certificate::UNSAT);
            }
            assert!(!asg.remains());
        }
        debug_assert_eq!(asg.decision_level(), asg.root_level());
        if elim.simplify(asg, cdb, rst, state, true).is_err() {
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
                if elim.simplify(asg, cdb, rst, state, false).is_err() {
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
                asg.dump_cnf(cdb, "last-step.cnf");

                // As a preparation for incremental solving, we need to backtrack to the
                // root level. So all assignments, including assignments to eliminated vars,
                // are stored in an extra storage. It has the same type of `AssignStack::assign`.
                #[cfg(feature = "boundary_check")]
                check(asg, cdb, true, "Before extending the model");

                let model = asg.extend_model(cdb, elim.eliminated_lits());

                #[cfg(feature = "boundary_check")]
                check(asg, cdb, true, "After extending the model");

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
                    .map(|(vi, _)| i32::from(Lit::from((vi, model[vi].unwrap()))))
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
                analyze_final(asg, state, &cdb[ci]);

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
    let mut current_stage: Option<bool> = Some(true);
    let mut num_learnt = 0;

    state.stm.initialize(
        (asg.derefer(assign::property::Tusize::NumUnassertedVar) as f64).sqrt() as usize,
    );
    while 0 < asg.derefer(assign::property::Tusize::NumUnassignedVar) || asg.remains() {
        if !asg.remains() {
            let lit = asg.select_decision_literal();
            asg.assign_by_decision(lit);
        }
        if let Err(cc) = asg.propagate(cdb) {
            if asg.decision_level() == asg.root_level() {
                return Err(SolverError::RootLevelConflict(cc));
            }
            asg.update_activity_tick();
            #[cfg(feature = "clause_rewarding")]
            cdb.update_activity_tick();
            if 1 < handle_conflict(asg, cdb, rst, state, &cc)? {
                num_learnt += 1;
            }
            if state.stm.stage_ended(num_learnt) {
                if let Some(p) = state.elapsed() {
                    if 1.0 <= p {
                        return Err(SolverError::TimeOut);
                    }
                } else {
                    return Err(SolverError::UndescribedError);
                }
                RESTART!(asg, rst);
                cdb.reduce(asg, state.stm.num_reducible());
                #[cfg(feature = "trace_equivalency")]
                cdb.check_consistency(asg, "before simplify");
                dump_stage(state, asg, rst, current_stage);
                let span_pre = state.stm.current_span();
                let next_stage: Option<bool> = state.stm.prepare_new_stage(
                    (asg.derefer(assign::property::Tusize::NumUnassignedVar) as f64).sqrt()
                        as usize,
                    num_learnt,
                );
                let scale = state.stm.current_scale();
                let max_scale = state.stm.max_scale();
                if let Some(new_segment) = next_stage {
                    asg.stage_scale = scale;
                    if cfg!(feature = "clause_vivification") {
                        cdb.vivify(asg, rst, state)?;
                    }
                    if new_segment {
                        asg.rescale_activity((max_scale - scale) as f64 / max_scale as f64);
                        if cfg!(feature = "clause_elimination") {
                            elim.simplify(asg, cdb, rst, state, false)?;
                        }
                        if cfg!(feature = "dynamic_restart_threshold") {
                            rst.adjust_threshold(span_pre, state.stm.current_segment());
                        }
                    }
                }
                asg.clear_asserted_literals(cdb)?;
                state.progress(asg, cdb, elim, rst);
                rst.set_sensibility(scale, state.stm.max_scale());
                asg.handle(SolverEvent::Stage(scale));
                current_stage = next_stage;
            } else if rst.restart(
                asg.refer(assign::property::TEma::AssignRate),
                cdb.refer(cdb::property::TEma::LBD),
            ) == Some(RestartDecision::Force)
            {
                RESTART!(asg, rst);
            }
            if let Some(na) = asg.best_assigned() {
                state.flush("");
                state.flush(format!("unreachable core: {}", na));
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

/// display the current stats. before updating stabiliation parameters
fn dump_stage(state: &mut State, asg: &AssignStack, rst: &Restarter, current_stage: Option<bool>) {
    let cycle = state.stm.current_cycle();
    let scale = state.stm.current_scale();
    let stage = state.stm.current_stage();
    let segment = state.stm.current_segment();
    state.log(
        asg.num_conflict,
        match current_stage {
            None => format!(
                "                   stg:{:>5}, scl:{:>4}, cpr:{:>9.2}",
                stage,
                scale,
                asg.refer(assign::property::TEma::ConflictPerRestart).get(),
            ),
            Some(false) => format!("         cyc:{:4}, stg:{:>5}", cycle, stage),
            Some(true) => format!(
                "seg:{:3}, cyc:{:4}, stg:{:>5}, rlt:{:>7.4}",
                segment,
                cycle,
                stage,
                rst.derefer(restart::property::Tf64::RestartThreshold),
            ),
        },
    );
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

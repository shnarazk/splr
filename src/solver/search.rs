//! Conflict-Driven Clause Learning Search engine
#[cfg(feature = "trail_saving")]
use crate::assign::TrailSavingIF;
use {
    super::{Certificate, Solver, SolverEvent, SolverResult, conflict::handle_conflict},
    crate::{
        assign::{
            self, AssignIF, AssignStack, PhaseRotation, PropagateIF, VarActivityScheme,
            VarManipulateIF, VarSelectIF,
        },
        cdb::{ClauseDB, ClauseDBIF, VivifyIF},
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
    ($asg: expr, $cdb: expr, $state: expr) => {{
        $asg.cancel_until($cdb, $asg.root_level());
        #[cfg(feature = "trail_saving")]
        {
            $asg.clear_saved_trail();
        }
        $cdb.handle(SolverEvent::Restart);
        $state.handle(SolverEvent::Restart);
        $asg.clear_asserted_literals($cdb)
    }};
    ($asg: expr, $cdb: expr, $state: expr, $_: expr) => {
        $asg.cancel_until($cdb, $asg.root_level());
        #[cfg(feature = "trail_saving")]
        {
            $asg.clear_saved_trail();
        }
        $cdb.handle(SolverEvent::Restart);
        $state.handle(SolverEvent::Restart);
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
        let Solver { asg, cdb, state } = self;
        if cdb.check_size().is_err() {
            return Err(SolverError::OutOfMemory);
        }
        state.progress_header();
        state.progress(asg, cdb);
        state.flush("");
        state.flush("Preprocessing stage: ");

        #[cfg(feature = "clause_vivification")]
        {
            state.flush("vivifying...");
            if cdb.vivify(asg, state).is_err() {
                state.log(None, "By vivifier as a pre-possessor");
                return Ok(Certificate::UNSAT);
            }
            debug_assert!(!asg.remains());
        }
        {
            debug_assert_eq!(asg.decision_level(), asg.root_level());
            let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
            if elim.simplify(asg, cdb, state, true).is_err() {
                if cdb.check_size().is_err() {
                    return Err(SolverError::OutOfMemory);
                }
                state.log(None, "By eliminator");
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
                        if m == 0 {
                            let l = Lit::from((vi, true));
                            debug_assert!(asg.assigned(l).is_none());
                            cdb.certificate_add_assertion(l);
                            if asg.assign_at_root_level(cdb, l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        } else if p == 0 {
                            let l = Lit::from((vi, false));
                            debug_assert!(asg.assigned(l).is_none());
                            cdb.certificate_add_assertion(l);
                            if asg.assign_at_root_level(cdb, l).is_err() {
                                return Ok(Certificate::UNSAT);
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
                    if elim.simplify(asg, cdb, state, false).is_err() {
                        // Why inconsistent? Because the CNF contains a conflict, not an error!
                        // Or out of memory.
                        state.progress(asg, cdb);
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
            asg.eliminated.append(elim.eliminated_lits());
            state[Stat::Simplify] += 1;
            state[Stat::SubsumedClause] = elim.num_subsumed;
        }
        //
        //## Search
        //
        state.progress(asg, cdb);
        let answer = search(asg, cdb, state);
        state.progress(asg, cdb);
        match answer {
            Ok(true) => {
                // As a preparation for incremental solving, we need to backtrack to the
                // root level. So all assignments, including assignments to eliminated vars,
                // are stored in an extra storage. It has the same type of `AssignStack::assign`.
                let model = asg.extend_model(cdb);

                // Run validator on the extended model.
                if cdb.validate(&model, false).is_some() {
                    state.log(None, "failed to validate the extended model");
                    state.progress(asg, cdb);
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
                RESTART!(asg, cdb, state, {});
                Ok(Certificate::SAT(vals))
            }
            Ok(false) | Err(SolverError::EmptyClause | SolverError::RootLevelConflict(_)) => {
                RESTART!(asg, cdb, state, {});
                Ok(Certificate::UNSAT)
            }
            Err(e) => {
                RESTART!(asg, cdb, state, {});
                state.progress(asg, cdb);
                Err(e)
            }
        }
    }
}

const PR_TBL: [(PhaseRotation, usize, usize); 6] = [
    (PhaseRotation::Best, 100_000, 1),
    (PhaseRotation::False, 100_000, 2),
    (PhaseRotation::True, 100_000, 3),
    (PhaseRotation::Random, 100_000, 4),
    (PhaseRotation::Inverted, 100_000, 5),
    (PhaseRotation::Walk, 100_000, 0),
];

/// main loop; returns `Ok(true)` for SAT, `Ok(false)` for UNSAT.
fn search(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
) -> Result<bool, SolverError> {
    let mut span_len: usize = 1;
    let mut processing_pressure: usize = 0;
    let processing_interval: usize = 10_000;
    let mut progress_pressure: usize = 0;
    let progress_interval: usize = 10_000;
    let mut reduction_pressure: usize = 0;
    let reduction_interval: usize = 10_000;
    let mut rephase_span: usize = 0;
    let mut current_phase: &(PhaseRotation, usize, usize) = &PR_TBL[0];
    let vmtf_interval: usize = 40_000;
    // a simple value checker
    let mut assign_peak: usize = 0;
    let luby_scale: usize = 8;
    let mut span_scale: usize = luby_scale;

    macro_rules! to_lrb {
        () => {
            if asg.activity_scheme != VarActivityScheme::LRB {
                asg.activity_scheme = VarActivityScheme::LRB;
                asg.set_learning_rate(state.config.vrw_learning_rate);
                asg.rebuild_order();
            }
            current_phase = &PR_TBL[0];
            asg.phase_mode = current_phase.0;
            rephase_span = 0;
        };
    }
    macro_rules! to_vmtf {
        () => {
            if asg.activity_scheme != VarActivityScheme::VMTF {
                asg.activity_scheme = VarActivityScheme::VMTF;
                asg.phase_mode = PhaseRotation::Walk;
                asg.set_learning_rate(0.0); // Don't change this
                asg.rebuild_order();
                rephase_span = 0;
            }
        };
    }
    macro_rules! rotate_rephase_mode {
        () => {
            if current_phase.2 == 0 {
                to_vmtf!();
            } else {
                current_phase = &PR_TBL[current_phase.2];
                asg.phase_mode = current_phase.0;
                rephase_span = 0;
            }
        };
    }
    macro_rules! reduce {
        () => {
            cdb.reduce(asg);
            reduction_pressure = 0;
            state.search_mode_ratio.0.update(0.0);
            state.search_mode_ratio.1.update(0.0);
        };
    }
    macro_rules! update_core {
        ($n: expr) => {
            asg.clear_asserted_literals(cdb)?;
            if let Some(core) = asg.check_best_phases() {
                assign_peak = assign_peak.saturating_sub(2 * $n);
                state.core_size = core;
            } else {
                assign_peak = 0;
                state.core_size = asg.derefer(assign::property::Tusize::NumUnassertedVar);
            }
        };
    }

    state.core_size = cdb.num_clause;
    state.span_manager.reset();
    while 0 < asg.derefer(assign::property::Tusize::NumUnassignedVar) || asg.remains() {
        if !asg.remains() {
            let lit = asg.select_decision_literal();
            asg.assign_by_decision(lit);
        }
        let Err(cc) = asg.propagate(cdb) else {
            continue;
        };
        if asg.decision_level() == asg.root_level() {
            return Err(SolverError::RootLevelConflict(cc));
        }
        asg.update_activity_tick();
        let (cid, lbd) = handle_conflict(asg, cdb, state, &cc)?;
        if cid == ClauseId::default() {
            match asg.activity_scheme {
                VarActivityScheme::LRB => {
                    state.search_mode_ratio.0.update(1.0);
                    state.search_mode_ratio.1.update(0.0);
                }
                VarActivityScheme::VMTF => {
                    state.search_mode_ratio.0.update(0.0);
                    state.search_mode_ratio.1.update(1.0);
                }
            }
            update_core!(1);
        } else {
            cdb.lbd.update(lbd as f64);
        }
        // not use '<=' to avoid an oscilation
        if assign_peak < asg.stack_len() {
            assign_peak = asg.stack_len();
            state.core_size = asg.save_best_phases();
        }
        reduction_pressure += (lbd > 4) as usize;
        processing_pressure += (lbd <= 5) as usize;
        progress_pressure += 1;
        span_len += 1;
        rephase_span += 1;
        if reduction_pressure >= reduction_interval * 8 {
            reduce!();
        }
        if state.span_manager.span_ended(span_len / span_scale) {
            span_len = 0;
            let new_segment = state.span_manager.prepare_new_span(span_len);
            dump_stage(asg, state, new_segment);
            if reduction_pressure >= reduction_interval {
                reduce!();
            }
            {
                let unasserted_pre = asg.derefer(assign::property::Tusize::NumUnassertedVar);
                RESTART!(asg, cdb, state)?;
                if processing_pressure >= processing_interval {
                    if cfg!(feature = "clause_vivification") {
                        cdb.vivify(asg, state)?;
                    }
                    if cfg!(feature = "clause_elimination") {
                        let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
                        state.flush("clause subsumption, ");
                        elim.simplify(asg, cdb, state, false)?;
                        asg.eliminated.append(elim.eliminated_lits());
                    }
                    processing_pressure = 0;
                }
                let unasserted_now = asg.derefer(assign::property::Tusize::NumUnassertedVar);
                if unasserted_now != unasserted_pre {
                    update_core!(unasserted_pre - unasserted_now);
                }
            }
            if cfg!(feature = "rephase") {
                match asg.activity_scheme {
                    VarActivityScheme::LRB if rephase_span >= current_phase.1 => {
                        rotate_rephase_mode!();
                    }
                    VarActivityScheme::VMTF if rephase_span >= vmtf_interval => {
                        to_lrb!();
                    }
                    _ => (),
                }
            }
            if new_segment == Some(true) {
                span_scale = luby_scale * state.span_manager.envelop_index();
            }
            // Adapt LRB learning rate to the upcoming Luby span length:
            // shorter spans → higher α (fast learning before the next restart),
            // longer spans  → lower  α (stable estimates over more conflicts).
            if asg.activity_scheme == VarActivityScheme::LRB {
                let span = state.span_manager.current_span() as f64;
                let adaptive_lr = (state.config.vrw_learning_rate / span.sqrt())
                    .clamp(1e-4, state.config.vrw_learning_rate);
                asg.set_learning_rate(adaptive_lr);
            }
        }
        if progress_pressure >= progress_interval {
            state.progress(asg, cdb);
            if let Some(p) = state.elapsed() {
                if 1.0 <= p {
                    return Err(SolverError::TimeOut);
                }
            } else {
                return Err(SolverError::UndescribedError);
            }
            progress_pressure = 0;
        }
    }
    state.log(
        None,
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
fn dump_stage(asg: &AssignStack, state: &mut State, shift: Option<bool>) {
    let cycle = state.span_manager.envelop_index();
    let span = state.span_manager.current_span();
    let stage = state.span_manager.current_segment();
    let segment = state.span_manager.current_segment();
    let cpr = asg.refer(assign::property::TEma::ConflictPerRestart).get();
    let vlr = asg.derefer(assign::property::Tf64::VarLearningRate);
    state.log(
        match shift {
            None => Some((None, None, stage)),
            Some(false) => Some((None, Some(cycle), stage)),
            Some(true) => Some((Some(segment), Some(cycle), stage)),
        },
        format!("{span:>7}, cpr:{cpr:>8.2}, vlr:{vlr:>3.2}"),
    );
}

//! Conflict-Driven Clause Learning Search engine
#[cfg(feature = "trail_saving")]
use crate::assign::TrailSavingIF;
use {
    super::{Certificate, Solver, SolverEvent, SolverResult, conflict::handle_conflict},
    crate::{
        assign::{self, AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarSelectIF},
        cdb::{self, ClauseDB, ClauseDBIF, VivifyIF},
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
    ($asg: expr, $cdb: expr, $state: expr) => {
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
                RESTART!(asg, cdb, state);
                Ok(Certificate::SAT(vals))
            }
            Ok(false) | Err(SolverError::EmptyClause | SolverError::RootLevelConflict(_)) => {
                RESTART!(asg, cdb, state);
                Ok(Certificate::UNSAT)
            }
            Err(e) => {
                RESTART!(asg, cdb, state);
                state.progress(asg, cdb);
                Err(e)
            }
        }
    }
}

#[derive(Default, Eq, PartialEq)]
enum SearchMode {
    Focus,
    Pursue,
    #[default]
    Explore,
}

/// main loop; returns `Ok(true)` for SAT, `Ok(false)` for UNSAT.
fn search(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
) -> Result<bool, SolverError> {
    let mut current_core: usize = 999_999;
    let mut core_was_rebuilt: Option<usize> = None;

    // monotonic increment counter
    let mut span_len: usize = 1;
    let cooling_len: usize = 20;
    let mut processing_pressure: usize = 0;
    let mut ruduction_pressure: usize = 0;
    let reduction_interval: usize = 40_000;
    let processing_interval: usize = 60_000;
    let mut progress_pressure: usize = 0;
    let progress_interval: usize = 10_000;
    let mut focusing: SearchMode = SearchMode::Explore;
    let mut cii_hist: Histogram = Histogram::default();
    let mut core_ema: Ema = Ema::new(20);
    let mut core_hist: Histogram = Histogram::default();

    state.span_manager.reset();
    while 0 < asg.derefer(assign::property::Tusize::NumUnassignedVar) || asg.remains() {
        if !asg.remains() {
            let lit = asg.select_decision_literal();
            asg.assign_by_decision(lit);
        }
        let Err(cc) = asg.propagate(cdb) else {
            continue;
        };
        progress_pressure += 1;
        span_len += 1;
        if asg.decision_level() == asg.root_level() {
            return Err(SolverError::RootLevelConflict(cc));
        }
        asg.update_activity_tick();
        #[cfg(feature = "clause_rewarding")]
        {
            cdb.update_activity_tick();
        }
        {
            let n = asg.derefer(assign::property::Tusize::NumUnassertedVar);
            let s = asg.len_upto(asg.decision_level().saturating_sub(1));
            core_ema.update(s as f64 / n as f64);
        }
        let lbd = handle_conflict(asg, cdb, state, &cc)?;
        match lbd.cmp(&1) {
            std::cmp::Ordering::Less => (),
            std::cmp::Ordering::Equal => (),
            std::cmp::Ordering::Greater => {
                ruduction_pressure += 1;
                processing_pressure += 1;
                cdb.lbd.update(lbd);
            }
        }
        if ruduction_pressure >= reduction_interval {
            cdb.reduce(asg, state.span_manager.envelop_index());
            ruduction_pressure = 0;
            cii_hist.rescale(0.95);
            core_hist.rescale(0.95);
        }

        if state
            .span_manager
            .span_ended(span_len.saturating_sub(cooling_len))
        {
            let r = cii_hist.add(asg.conflict_interval_index.get());
            let s = core_hist.add(core_ema.get());
            if (focusing != SearchMode::Focus && r < 0.05)
                || (focusing == SearchMode::Focus && r < 0.2)
            {
                if focusing != SearchMode::Focus {
                    focusing = SearchMode::Focus;
                    asg.set_learning_rate(0.0);
                    asg.use_conflict_order(true);
                }
                state.search_mode_ratio.0.update(1.0);
                state.search_mode_ratio.1.update(0.0);
                state.search_mode_ratio.2.update(0.0);
            } else if (focusing != SearchMode::Pursue && r > 0.95)
                || (focusing == SearchMode::Pursue && r > 0.8)
            {
                if focusing != SearchMode::Pursue {
                    focusing = SearchMode::Pursue;
                    asg.set_learning_rate(state.config.vrw_learning_rate);
                    asg.use_conflict_order(false);
                }
                state.search_mode_ratio.0.update(0.0);
                state.search_mode_ratio.1.update(1.0);
                state.search_mode_ratio.2.update(0.0);
            } else {
                if focusing != SearchMode::Explore {
                    focusing = SearchMode::Explore;
                    asg.set_learning_rate(state.config.vrw_learning_rate);
                    asg.use_conflict_order(false);
                }
                RESTART!(asg, cdb, state);
                asg.clear_asserted_literals(cdb)?;
                state.search_mode_ratio.0.update(0.0);
                state.search_mode_ratio.1.update(0.0);
                state.search_mode_ratio.2.update(1.0);
            }
            span_len = 0;
            let new_span = state.span_manager.prepare_new_span(span_len);
            dump_stage(asg, cdb, state, new_span);

            if asg.decision_level() == asg.root_level {
                #[cfg(feature = "rephase")]
                if focusing == SearchMode::Explore && s < 0.3 {
                    asg.select_rephasing_target();
                }
                if processing_pressure >= processing_interval {
                    let mut n = usize::MAX;
                    while asg.derefer(assign::property::Tusize::NumUnassertedVar) < n {
                        n = asg.derefer(assign::property::Tusize::NumUnassertedVar);
                        if cfg!(feature = "clause_vivification") {
                            let mut m = usize::MAX;
                            while asg.derefer(assign::property::Tusize::NumUnassertedVar) < m {
                                m = asg.derefer(assign::property::Tusize::NumUnassertedVar);
                                cdb.vivify(asg, state)?;
                            }
                        }
                        if cfg!(feature = "clause_elimination") {
                            let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
                            state.flush("clause subsumption, ");
                            elim.simplify(asg, cdb, state, false)?;
                            asg.eliminated.append(elim.eliminated_lits());
                            state.flush("");
                        }
                    }
                    processing_pressure = 0;
                }
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
        if let Some(na) = asg.best_assigned() {
            if current_core < na && core_was_rebuilt.is_none() {
                core_was_rebuilt = Some(current_core);
            }
            current_core = na;
            state.flush("");
            state.flush(format!("unreachable core: {na} "));
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
fn dump_stage(asg: &AssignStack, cdb: &mut ClauseDB, state: &mut State, shift: Option<bool>) {
    let cycle = state.span_manager.envelop_index();
    let span = state.span_manager.current_span();
    let stage = state.span_manager.current_segment();
    let segment = state.span_manager.current_segment();
    let cpr = asg.refer(assign::property::TEma::ConflictPerRestart).get();
    let vlr = asg.derefer(assign::property::Tf64::VarLearningRate);
    let cdt = cdb.derefer(cdb::property::Tf64::ReductionThreshold);
    state.log(
        match shift {
            None => Some((None, None, stage)),
            Some(false) => Some((None, Some(cycle), stage)),
            Some(true) => Some((Some(segment), Some(cycle), stage)),
        },
        format!("{span:>7}, cpr:{cpr:>8.2}, vlr:{vlr:>3.2}, cdt:{cdt:>5.2}"),
    );
}

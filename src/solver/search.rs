//! Conflict-Driven Clause Learning Search engine
use {
    super::{
        Certificate, Solver, SolverEvent, SolverResult, conflict::handle_conflict,
        restart::RestartIF,
    },
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

/// main loop; returns `Ok(true)` for SAT, `Ok(false)` for UNSAT.
fn search(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
) -> Result<bool, SolverError> {
    let mut previous_span: Option<bool> = Some(true);
    let mut current_core: usize = 999_999;
    let mut core_was_rebuilt: Option<usize> = None;
    #[cfg(feature = "rephase")]
    let mut sls_core = cdb.derefer(cdb::property::Tusize::NumClause);
    let mut after_restart: usize = 0;
    let mut num_learnts: usize = 0;
    let mut restart_pressure: usize = 0;
    let restart_interval: usize = 40_000;
    let mut lbd_threshold: f64 = 0.0;
    let mut processing_pressure: usize = 0;
    let processing_interval: usize = 80_000;
    let cooling_length: usize = 4;
    let mut count: usize = 0;

    state.stm.reset();
    asg.update_activity_decay(0.98);
    while 0 < asg.derefer(assign::property::Tusize::NumUnassignedVar) || asg.remains() {
        if !asg.remains() {
            let lit = asg.select_decision_literal();
            asg.assign_by_decision(lit);
        }
        let Err(cc) = asg.propagate(cdb) else {
            continue;
        };
        count += 1;
        after_restart += 1;
        if asg.decision_level() == asg.root_level() {
            return Err(SolverError::RootLevelConflict(cc));
        }
        asg.update_activity_tick();
        #[cfg(feature = "clause_rewarding")]
        cdb.update_activity_tick();
        let lbd = handle_conflict(asg, cdb, state, &cc)?;
        if lbd == 0 {
            restart_pressure += 1;
        } else if 1 < lbd {
            num_learnts += 1;
            if after_restart >= cooling_length {
                if restart_pressure == 0 {
                    lbd_threshold = cdb.lbd.get_fast();
                    cdb.lbd.update(lbd);
                }
                restart_pressure += (lbd >= lbd_threshold as u16) as usize;
            } else {
                // we don't want to use the value under the extended search mode
                cdb.lbd.update(lbd);
            }
            if num_learnts >= restart_interval.max(state.stm.envelop_index() * 10_000) {
                cdb.reduce(asg, state.stm.envelop_index());
                num_learnts = 0;
            }
        }
        processing_pressure += 1;

        if state.stm.span_ended(restart_pressure) {
            if let Some(p) = state.elapsed() {
                if 1.0 <= p {
                    return Err(SolverError::TimeOut);
                }
            } else {
                return Err(SolverError::UndescribedError);
            }
            after_restart = 0;
            restart_pressure = 0;
            lbd_threshold = 0.0;
            RESTART!(asg, cdb, state);
            #[cfg(feature = "rephase")]
            {
                asg.select_rephasing_target();
            }
            asg.clear_asserted_literals(cdb)?;

            dump_stage(asg, cdb, state, previous_span);
            let new_span: Option<bool> = state.stm.prepare_new_span(restart_pressure);
            let segment_length = state.stm.current_segment_length();
            if let Some(new_envelope) = new_span {
                // a beginning of a new cycle
                {
                    // Longer segments reduces learning rates to search deeper space.
                    let index_e = 10.0;
                    let index_s =
                        state.stm.current_segment() - state.stm.envelope_starting_segment();
                    let decay_index: f64 = index_e + index_s as f64;
                    asg.update_activity_decay(1.0 - 1.0 / decay_index);
                }

                #[cfg(feature = "rephase")]
                {
                    if cfg!(feature = "stochastic_local_search") {
                        use cdb::StochasticLocalSearchIF;
                        macro_rules! sls {
                            ($assign: expr, $limit: expr) => {
                                state.sls_index += 1;
                                state.flush(format!(
                                    "SLS(#{}, core: {}, steps: {})",
                                    state.sls_index, sls_core, $limit
                                ));
                                let cls = cdb.stochastic_local_search(asg, &mut $assign, $limit);
                                asg.override_rephasing_target(&$assign);
                                sls_core = sls_core.min(cls.1);
                            };
                            ($assign: expr, $improved: expr, $limit: expr) => {
                                state.sls_index += 1;
                                state.flush(format!(
                                    "SLS(#{}, core: {}, steps: {})",
                                    state.sls_index, sls_core, $limit
                                ));
                                let cls = cdb.stochastic_local_search(asg, &mut $assign, $limit);
                                asg.reward_by_sls(&$assign);
                                if $improved(cls) {
                                    asg.override_rephasing_target(&$assign);
                                }
                                sls_core = sls_core.min(cls.1);
                            };
                        }
                        macro_rules! scale {
                            ($a: expr, $b: expr) => {
                                ($a.saturating_sub($b.next_power_of_two().trailing_zeros()) as f64)
                                    .powf(1.75) as usize
                                    + 1
                            };
                        }
                        let ent = cdb.refer(cdb::property::TEma::Entanglement).get() as usize;
                        let n = cdb.derefer(cdb::property::Tusize::NumClause);
                        if let Some(c) = core_was_rebuilt {
                            core_was_rebuilt = None;
                            if c < current_core {
                                let steps = scale!(27_u32, c) * scale!(24_u32, n) / ent;
                                let mut assignment = asg.best_phases_ref(Some(false));
                                sls!(assignment, steps);
                            }
                        } else if new_envelope {
                            let n = cdb.derefer(cdb::property::Tusize::NumClause);
                            let steps = scale!(27_u32, current_core) * scale!(24_u32, n) / ent;
                            let mut assignment = asg.best_phases_ref(Some(false));
                            sls!(assignment, steps);
                        }
                    }
                    asg.select_rephasing_target();
                }
                if processing_pressure >= processing_interval {
                    if cfg!(feature = "clause_vivification") {
                        cdb.vivify(asg, state)?;
                    }
                    if cfg!(feature = "clause_elimination") {
                        let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
                        state.flush("clause subsumption, ");
                        elim.simplify(asg, cdb, state, false)?;
                        asg.eliminated.append(elim.eliminated_lits());
                        state[Stat::Simplify] += 1;
                        state[Stat::SubsumedClause] = elim.num_subsumed;
                    }
                    processing_pressure = 0;
                }
                if new_envelope {
                    {
                        let base = state.stm.current_segment();
                        let decay_index: f64 = (20 + 2 * base) as f64;
                        asg.update_activity_decay((decay_index - 1.0) / decay_index);
                    }
                }
            }

            if num_learnts > restart_interval {
                cdb.reduce(asg, state.stm.envelop_index());
                num_learnts = 0;
            }

            asg.handle(SolverEvent::Stage(segment_length));
            state.restart.set_stage_parameters(segment_length);
            previous_span = new_span;
        }
        if count.is_multiple_of(10_000) {
            state.progress(asg, cdb);
            if state.stm.current_span() >= 8192 {
                state.flush("deep search...");
            }
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
    let active = true; // state.rst.enable;
    let cycle = state.stm.envelop_index();
    let span = state.stm.current_span();
    let stage = state.stm.current_segment();
    let segment = state.stm.current_segment();
    let cpr = asg.refer(assign::property::TEma::ConflictPerRestart).get();
    let vdr = asg.derefer(assign::property::Tf64::VarDecayRate);
    let cdt = cdb.derefer(cdb::property::Tf64::ReductionThreshold);
    let fuel = if active {
        state.restart.penetration_energy_charged
    } else {
        f64::NAN
    };
    state.log(
        match shift {
            None => Some((None, None, stage)),
            Some(false) => Some((None, Some(cycle), stage)),
            Some(true) => Some((Some(segment), Some(cycle), stage)),
        },
        format!("{span:>7}, fuel:{fuel:>9.2}, cpr:{cpr:>8.2}, vdr:{vdr:>3.2}, cdt:{cdt:>5.2}"),
    );
}

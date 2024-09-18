//! Conflict-Driven Clause Learning Search engine
use {
    super::{conflict::handle_conflict, Certificate, Solver, SolverEvent, SolverResult},
    crate::{
        assign::{self, AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarSelectIF},
        cdb::{self, ClauseDB, ClauseDBIF, VivifyIF},
        processor::{EliminateIF, Eliminator},
        state::{Stat, State, StateIF},
        types::*,
    },
};

const STAGE_SIZE: usize = 32;

#[derive(Debug, Default, PartialEq, PartialOrd)]
pub struct SearchState {
    num_reduction: usize,
    reduce_step: usize,
    next_reduce: usize,
    current_core: usize,
    current_span: usize,
    from_segment_beginning: usize,
    core_was_rebuilt: Option<usize>,
    previous_stage: Option<bool>,
    elapsed_time: f64,
    reduce_threshold: f64,

    #[cfg(feature = "rephase")]
    sls_core: usize,
    #[cfg(feature = "graph_view")]
    pub span_history: Vec<usize>,
}

impl SearchState {
    pub fn current_core(&self) -> usize {
        self.current_core
    }
    pub fn current_span(&self) -> usize {
        self.current_span
    }
}

/// API to [`solve`](`crate::solver::SolveIF::solve`) SAT problems.
pub trait SolveIF {
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solve(&mut self) -> SolverResult;
    /// 1st part of solve
    /// returns `None' if solver can proceed to `step_search`
    fn prepare(&mut self) -> Result<SearchState, Result<Certificate, SolverError>>;
    /// main part of solve
    /// returns `None' if solver can repeat `step_search`
    fn search_stage(&mut self, ss: &mut SearchState) -> Result<Option<bool>, SolverError>;
    /// last part of solve
    fn postprocess(&mut self, result: Result<bool, SolverError>) -> SolverResult;
    /// standard logger
    fn progress(&mut self);
}

macro_rules! RESTART {
    ($asg: expr, $cdb: expr, $state: expr) => {
        $asg.cancel_until($asg.root_level());
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
    #[cfg(not(feature = "interleave"))]
    fn solve(&mut self) -> SolverResult {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut state,
        } = self;
        if cdb.check_size().is_err() {
            return Err(SolverError::OutOfMemory);
        }
        #[cfg(feature = "incremental_solver")]
        {
            // Reinitialize AssignStack::var_order with respect for assignments.
            asg.rebuild_order();
        }
        state.progress_header();
        state.progress(asg, cdb);
        state.flush("");
        state.flush("Preprocessing stage: ");

        #[cfg(feature = "clause_vivification")]
        {
            state.flush("vivifying...");
            if cdb.vivify(asg, state).is_err() {
                #[cfg(feature = "support_user_assumption")]
                analyze_final(asg, state, &cdb[ci]);

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

            #[cfg(all(feature = "clause_elimination", not(feature = "incremental_solver")))]
            {
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
                                debug_assert!(asg.assigned(l).is_none());
                                cdb.certificate_add_assertion(l);
                                if asg.assign_at_root_level(l).is_err() {
                                    return Ok(Certificate::UNSAT);
                                }
                            } else if p == 0 {
                                let l = Lit::from((vi, false));
                                debug_assert!(asg.assigned(l).is_none());
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
                #[cfg(feature = "trace_equivalency")]
                asg.dump_cnf(cdb, "last-step.cnf");

                // As a preparation for incremental solving, we need to backtrack to the
                // root level. So all assignments, including assignments to eliminated vars,
                // are stored in an extra storage. It has the same type of `AssignStack::assign`.
                #[cfg(feature = "boundary_check")]
                check(asg, cdb, true, "Before extending the model");

                let model = asg.extend_model(cdb);

                #[cfg(feature = "boundary_check")]
                check(asg, cdb, true, "After extending the model");

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
                #[cfg(feature = "support_user_assumption")]
                analyze_final(asg, state, &cdb[ci]);

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
    #[cfg(feature = "interleave")]
    fn solve(&mut self) -> SolverResult {
        let mut ss = match self.prepare() {
            Ok(ss) => ss,
            Err(e) => return e,
        };
        self.progress();
        loop {
            match self.search_stage(&mut ss) {
                Ok(None) => {}
                Ok(Some(b)) => {
                    self.progress();
                    return self.postprocess(Ok(b));
                }
                Err(e) => {
                    self.progress();
                    return self.postprocess(Err(e));
                }
            }
        }
    }
    fn prepare(&mut self) -> Result<SearchState, Result<Certificate, SolverError>> {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut state,
        } = self;
        if cdb.check_size().is_err() {
            return Err(Err(SolverError::OutOfMemory));
        }
        #[cfg(feature = "incremental_solver")]
        {
            // Reinitialize AssignStack::var_order with respect for assignments.
            asg.rebuild_order();
        }
        state.progress_header();
        state.progress(asg, cdb);
        state.flush("");
        state.flush("Preprocessing stage: ");

        #[cfg(feature = "clause_vivification")]
        {
            state.flush("vivifying...");
            if cdb.vivify(asg, state).is_err() {
                #[cfg(feature = "support_user_assumption")]
                analyze_final(asg, state, &cdb[ci]);

                state.log(None, "By vivifier as a pre-possessor");
                return Err(Ok(Certificate::UNSAT));
            }
            debug_assert!(!asg.remains());
        }
        #[cfg(all(feature = "clause_elimination", not(feature = "incremental_solver")))]
        {
            debug_assert_eq!(asg.decision_level(), asg.root_level());
            let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
            if elim.simplify(asg, cdb, state, true).is_err() {
                if cdb.check_size().is_err() {
                    return Err(Err(SolverError::OutOfMemory));
                }
                state.log(None, "By eliminator");
                return Err(Ok(Certificate::UNSAT));
            }

            // #[cfg(all(feature = "clause_elimination", not(feature = "incremental_solver")))]
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
                                debug_assert!(asg.assigned(l).is_none());
                                cdb.certificate_add_assertion(l);
                                if asg.assign_at_root_level(l).is_err() {
                                    return Err(Ok(Certificate::UNSAT));
                                }
                            } else if p == 0 {
                                let l = Lit::from((vi, false));
                                debug_assert!(asg.assigned(l).is_none());
                                cdb.certificate_add_assertion(l);
                                if asg.assign_at_root_level(l).is_err() {
                                    return Err(Ok(Certificate::UNSAT));
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
                    if elim.simplify(asg, cdb, state, false).is_err() {
                        // Why inconsistent? Because the CNF contains a conflict, not an error!
                        // Or out of memory.
                        state.progress(asg, cdb);
                        if cdb.check_size().is_err() {
                            return Err(Err(SolverError::OutOfMemory));
                        }
                        return Err(Ok(Certificate::UNSAT));
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
        state.stm.initialize(STAGE_SIZE);
        let nv: u32 = asg.derefer(assign::Tusize::NumUnassertedVar).max(1).ilog2();
        let nc: u32 = cdb
            .iter()
            .filter(|c| !c.is_dead() && 2 < c.len())
            .count()
            .max(1)
            .ilog2();

        Ok(SearchState {
            num_reduction: 0,
            reduce_step: (nv + nc) as usize,
            next_reduce: 64,
            from_segment_beginning: 0,
            current_core: asg.derefer(assign::property::Tusize::NumUnassertedVar),
            current_span: 1,
            core_was_rebuilt: None,
            previous_stage: None,
            elapsed_time: 0.0,
            reduce_threshold: 10000.0,
            #[cfg(feature = "rephase")]
            sls_core: cdb.derefer(cdb::property::Tusize::NumClause),
            #[cfg(feature = "graph_view")]
            span_history: Vec::new(),
        })
    }
    fn search_stage(&mut self, ss: &mut SearchState) -> Result<Option<bool>, SolverError> {
        // main loop; returns `Ok(true)` for SAT, `Ok(false)` for UNSAT.
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut state,
        } = self;

        state.flush("");
        while 0 < asg.derefer(assign::property::Tusize::NumUnassignedVar) || asg.remains() {
            if !asg.remains() {
                let lit = asg.select_decision_literal();
                asg.assign_by_decision(lit);
            }
            let Err(cc) = asg.propagate(cdb, false) else {
                continue;
            };
            if asg.decision_level() == asg.root_level() {
                return Err(SolverError::RootLevelConflict(cc));
            }
            asg.update_activity_tick();

            #[cfg(feature = "clause_rewarding")]
            cdb.update_activity_tick();

            if asg.root_level() == handle_conflict(asg, cdb, state, &cc)? {
                // let nv: u32 = asg.derefer(assign::Tusize::NumUnassertedVar).ilog2();
                // let nc: u32 = cdb
                //     .iter()
                //     .filter(|c| !c.is_dead() && 2 < c.len())
                //     .count()
                //     .ilog2();
                // ss.reduce_step = ((nv + nc) as usize + ss.reduce_step) / 2;
            }
            ss.from_segment_beginning += 1;
            if ss.current_span <= ss.from_segment_beginning {
                let with_restart = 1.0 < cdb.refer(cdb::property::TEma::LBD).trend();
                ss.from_segment_beginning = 0;

                #[cfg(feature = "graph_view")]
                ss.span_history.push(ss.current_span);

                let next_stage: Option<bool> = state
                    .stm
                    .prepare_new_stage(asg.derefer(assign::Tusize::NumConflict));
                if with_restart || next_stage.is_some() {
                    RESTART!(asg, cdb, state);

                    #[cfg(any(feature = "best_phases_tracking", feature = "rephase"))]
                    if ss.with_rephase {
                        asg.select_rephasing_target();
                        asg.clear_asserted_literals(cdb)?;
                        if next_stage == Some(true) {
                            ss.with_rephase = false;
                        }
                    }

                    #[cfg(feature = "trace_equivalency")]
                    cdb.check_consistency(asg, "before simplify");
                }
                ss.current_span = state.stm.current_span() as usize;
                let scale = state.stm.current_scale();
                asg.handle(SolverEvent::Stage(scale));
                if let Some(new_segment) = next_stage {
                    // a beginning of a new cycle
                    if cfg!(feature = "reward_annealing") {
                        const SLOP: f64 = 2.0;
                        let stm = &state.stm;
                        // let sigma = |x: f64| 1.0 / (1.0 + (-x).exp());
                        let sgm = |x: f64| x / (1.0 + x.abs());
                        let b: f64 = stm.segment_starting_cycle() as f64;
                        let n: f64 = stm.current_cycle() as f64 - b;
                        let m: f64 = 0.5 * b;
                        let k: f64 = (stm.current_segment() as f64).log2();
                        const R: (f64, f64) = (0.86, 0.995);
                        let d: f64 = {
                            let o: f64 = SLOP;
                            R.1 - (R.1 - R.0) * o / (k + o)
                        };
                        // assert_eq!(d, d.clamp(R.0, R.1));
                        let x: f64 = (1.0 + k) * (n - m) / m;
                        asg.update_activity_decay(1.0 + 0.5 * (sgm(x) - 1.0) * (1.0 - d));
                    }
                    state
                        .stm
                        .set_span_base(state.c_lvl.get_slow() - state.b_lvl.get_slow());
                    dump_stage(asg, cdb, state, &ss.previous_stage);

                    #[cfg(feature = "rephase")]
                    rephase(asg, cdb, state, ss);

                    let num_restart = asg.derefer(assign::Tusize::NumRestart);
                    if ss.next_reduce <= num_restart {
                        let stm = &state.stm;
                        let b: f64 = stm.segment_starting_cycle() as f64;
                        let n: f64 = 1.0 + stm.current_cycle() as f64 - b;
                        let ent: f64 = cdb.refer(cdb::property::TEma::Entanglement).get_slow();
                        let lbd: f64 = cdb.refer(cdb::property::TEma::LBD).get_slow();
                        // let val: f64 = 2.5 + 2.0 * (ent + lbd) / n.log2();
                        let min: f64 = ent.min(lbd);
                        let max: f64 = ent.max(lbd);
                        let val: f64 = 0.5 * min + max / n.sqrt();
                        state.extra_f64 = val;
                        cdb.reduce(asg, (val) as DecisionLevel);
                        /* ss.reduce_threshold = if state.stm.current_segment() < 8 {
                            40.0 - state.stm.current_segment() as f64
                        } else {
                            ss.reduce_threshold
                                .min(cdb.refer(cdb::property::TEma::Entanglement).get())
                        };
                        cdb.reduce(asg, ss.reduce_threshold as DecisionLevel / 2); */
                        ss.num_reduction += 1;
                        ss.reduce_step += 1;
                        ss.next_reduce = ss.reduce_step + num_restart;
                        if cfg!(feature = "clause_vivification") {
                            cdb.vivify(asg, state)?;
                        }
                        if cfg!(feature = "clause_elimination")
                            && !cfg!(feature = "incremental_solver")
                            && ss.num_reduction % 8 == 0
                        {
                            let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
                            state.flush("clause subsumption, ");
                            elim.simplify(asg, cdb, state, false)?;
                            asg.eliminated.append(elim.eliminated_lits());
                            state[Stat::Simplify] += 1;
                            state[Stat::SubsumedClause] = elim.num_subsumed;
                        }
                    }
                    if new_segment {
                        state.exploration_rate_ema.update(1.0);
                    }
                    if let Some(p) = state.elapsed() {
                        if ss.elapsed_time + 0.5 / state.config.c_timeout < p {
                            if 1.0 <= p {
                                return Err(SolverError::TimeOut);
                            }
                            state.progress(asg, cdb);
                            ss.previous_stage = next_stage;
                            ss.elapsed_time = p;
                            return Ok(None);
                        }
                        state.flush("");
                    } else {
                        return Err(SolverError::UndescribedError);
                    }
                }
            }
            if let Some(na) = asg.best_assigned() {
                if ss.current_core < na && ss.core_was_rebuilt.is_none() {
                    ss.core_was_rebuilt = Some(ss.current_core);
                }
                ss.current_core = na;
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
        Ok(Some(true))
    }
    fn postprocess(&mut self, answer: Result<bool, SolverError>) -> SolverResult {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut state,
        } = self;
        // let mut ss = SearchState::default();
        state.progress(asg, cdb);
        match answer {
            Ok(true) => {
                #[cfg(feature = "trace_equivalency")]
                asg.dump_cnf(cdb, "last-step.cnf");

                // As a preparation for incremental solving, we need to backtrack to the
                // root level. So all assignments, including assignments to eliminated vars,
                // are stored in an extra storage. It has the same type of `AssignStack::assign`.
                #[cfg(feature = "boundary_check")]
                check(asg, cdb, true, "Before extending the model");

                let model = asg.extend_model(cdb);

                #[cfg(feature = "boundary_check")]
                check(asg, cdb, true, "After extending the model");

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
                #[cfg(feature = "support_user_assumption")]
                analyze_final(asg, state, &cdb[ci]);

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
    fn progress(&mut self) {
        let Solver {
            ref asg,
            ref cdb,
            ref mut state,
        } = self;
        state.progress(asg, cdb);
    }
}

/// display the current stats. before updating stabiliation parameters
fn dump_stage(asg: &AssignStack, _cdb: &mut ClauseDB, state: &mut State, shift: &Option<bool>) {
    let cycle = state.stm.current_cycle();
    let span = state.stm.current_span();
    let stage = state.stm.current_stage();
    let segment = state.stm.current_segment();
    let cpr = asg.refer(assign::property::TEma::ConflictPerRestart).get();
    let vdr = asg.derefer(assign::property::Tf64::VarDecayRate);
    state.log(
        match shift {
            None => Some((None, None, stage)),
            Some(false) => Some((None, Some(cycle), stage)),
            Some(true) => Some((Some(segment), Some(cycle), stage)),
        },
        format!("{span:>7}, cpr:{cpr:>8.2}, vdr:{vdr:>3.2}"),
    );
}

#[cfg(feature = "rephase")]
fn rephase(asg: &mut AssignStack, cdb: &mut ClauseDB, state: &mut State, ss: &mut SearchState) {
    if cfg!(feature = "stochastic_local_search") {
        use cdb::StochasticLocalSearchIF;
        macro_rules! sls {
            ($assign: expr, $limit: expr) => {
                state.sls_index += 1;
                state.flush(format!(
                    "SLS(#{}, core: {}, steps: {})",
                    state.sls_index, ss.sls_core, $limit
                ));
                let cls = cdb.stochastic_local_search(asg, &mut $assign, $limit);
                asg.override_rephasing_target(&$assign);
                ss.sls_core = ss.sls_core.min(cls.1);
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
                ($a.saturating_sub($b.next_power_of_two().trailing_zeros()) as f64).powf(1.75)
                    as usize
                    + 1
            };
        }
        let ent = cdb.refer(cdb::property::TEma::Entanglement).get() as usize;
        let n = cdb.derefer(cdb::property::Tusize::NumClause);
        if let Some(c) = ss.core_was_rebuilt {
            ss.core_was_rebuilt = None;
            if c < ss.current_core {
                let steps = scale!(27_u32, c) * scale!(24_u32, n) / ent;
                let mut assignment = asg.best_phases_ref(Some(false));
                sls!(assignment, steps);
            }
        } else {
            let n = cdb.derefer(cdb::property::Tusize::NumClause);
            let steps = scale!(27_u32, ss.current_core) * scale!(24_u32, n) / ent;
            let mut assignment = asg.best_phases_ref(Some(false));
            sls!(assignment, steps);
        }
    }
    asg.select_rephasing_target();
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

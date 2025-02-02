//! Conflict-Driven Clause Learning Search engine
use {
    super::{
        conflict::handle_conflict, propagate::*, restart::RestartIF, Certificate, Solver,
        SolverEvent, SolverResult,
    },
    crate::{
        assign::{self, AssignIF, AssignStack},
        cdb::{self, ClauseDB, ClauseDBIF, ReductionType}, // , VivifyIF},
        // processor::{EliminateIF, Eliminator},
        state::{Stat, State, StateIF},
        types::*,
        var_activity::{VarActivityManager, VarActivityManagerIF},
    },
};

/// API to [`solve`](`crate::solver::SolveIF::solve`) SAT problems.
pub trait SolveIF<'a> {
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solve(&'a mut self) -> SolverResult;
}

macro_rules! RESTART {
    ($vars: expr, $asg: expr, $vam: expr, $cdb: expr, $state: expr) => {
        cancel_until($vars, $asg, $vam, $asg.root_level());
        $cdb.handle(SolverEvent::Restart);
        $state.handle(SolverEvent::Restart);
    };
}

impl<'a> SolveIF<'a> for Solver<'a> {
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
    fn solve(&'a mut self) -> SolverResult {
        // let Solver {
        //     vars,
        //     asg,
        //     vam,
        //     cdb,
        //     state,
        //     ..
        // } = self;
        let vars: &'a mut Vec<Var<'a>> = &mut self.vars;
        let asg: &'a mut AssignStack<'a> = &mut self.asg;
        let vam: &'a mut VarActivityManager = &mut self.vam;
        let cdb: &'a mut ClauseDB<'a> = &mut self.cdb;
        let state: &'a mut State<'a> = &mut self.state;
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
                #[cfg(feature = "support_user_assumption")]
                analyze_final(asg, state, &cdb[ci]);

                state.log(None, "By vivifier as a pre-possessor");
                return Ok(Certificate::UNSAT);
            }
            debug_assert!(!asg.remains());
        }
        {
            // debug_assert_eq!(asg.decision_level(), asg.root_level());
            // let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
            // if elim.simplify(asg, cdb, state, true).is_err() {
            //     if cdb.check_size().is_err() {
            //         return Err(SolverError::OutOfMemory);
            //     }
            //     state.log(None, "By eliminator");
            //     return Ok(Certificate::UNSAT);
            // }

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
                for v in vars.iter_mut().skip(1) {
                    if v.assign.is_some() {
                        continue;
                    }
                    if let Some((p, m)) = elim.stats(v.id) {
                        // We can't call `asg.assign_at_root_level(l)` even if p or m == 0.
                        // This means we can't pick `!l`.
                        // This becomes a problem in the case of incremental solving.
                        if m == 0 {
                            let l = Lit::from((v, false));
                            let lit = Literal::from(l);
                            cdb.certificate_add_assertion(lit);
                            if asg.assign_at_root_level(l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        } else if p == 0 {
                            let l = Lit::from((v, true));
                            let lit = Literal::from(l);
                            cdb.certificate_add_assertion(lit);
                            if asg.assign_at_root_level(l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        }
                        v.set(FlagVar::PHASE, m < p);
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
                    for v in vars.iter_mut().skip(1) {
                        if v.assign.is_some() || v.is(FlagVar::ELIMINATED) {
                            continue;
                        }
                        match elim.stats(v.id) {
                            Some((_, 0)) => (),
                            Some((0, _)) => (),
                            Some((p, m)) if m * 10 < p => v.turn_on(FlagVar::PHASE),
                            Some((p, m)) if p * 10 < m => v.turn_off(FlagVar::PHASE),
                            _ => (),
                        }
                    }
                    let act = 1.0 / (asg.num_vars as f64).powf(0.25);
                    for v in vars.iter_mut().skip(1) {
                        if !v.is(FlagVar::ELIMINATED) {
                            v.activity = act;
                        }
                    }
                    asg.rebuild_order();
                }
            }
            // asg.eliminated.append(elim.eliminated_lits());
            // state[Stat::Simplify] += 1;
            // state[Stat::SubsumedClause] = elim.num_subsumed;
        }
        //
        //## Search
        //
        state.progress(asg, cdb);
        let answer = search(vars, asg, vam, cdb, state).clone();
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

                let model = extend_model(vars, cdb);

                #[cfg(feature = "boundary_check")]
                check(asg, cdb, true, "After extending the model");

                // Run validator on the extended model.
                if cdb.validate(&model, false).is_some() {
                    state.log(None, "failed to validate the extended model");
                    state.progress(asg, cdb);
                    return Err(SolverError::SolverBug);
                }

                // map `Option<bool>` to `i32`, and remove the dummy var at the head.
                let vals = vars
                    .iter()
                    .enumerate()
                    .skip(1)
                    .map(|(vi, v)| i32::from(Lit::from((v, model[vi].unwrap()))))
                    .collect::<Vec<i32>>();

                // As a preparation for incremental solving, turn flags off.
                for v in vars.iter_mut().skip(1) {
                    if v.is(FlagVar::ELIMINATED) {
                        v.turn_off(FlagVar::ELIMINATED);
                    }
                }
                RESTART!(vars, asg, vam, cdb, state);
                Ok(Certificate::SAT(vals))
            }
            Ok(false) | Err(SolverError::EmptyClause | SolverError::RootLevelConflict) => {
                #[cfg(feature = "support_user_assumption")]
                analyze_final(asg, state, &cdb[ci]);

                RESTART!(vars, asg, vam, cdb, state);
                Ok(Certificate::UNSAT)
            }
            Err(e) => {
                RESTART!(vars, asg, vam, cdb, state);
                state.progress(asg, cdb);
                Err(e)
            }
        }
    }
}

/// main loop; returns `Ok(true)` for SAT, `Ok(false)` for UNSAT.
fn search<'a>(
    vars: &'a mut [Var<'a>],
    asg: &'a mut AssignStack<'a>,
    vam: &'a mut VarActivityManager,
    cdb: &'a mut ClauseDB<'a>,
    state: &mut State<'a>,
) -> Result<bool, SolverError> {
    let mut previous_stage: Option<bool> = Some(true);
    let mut num_learnt = 0;
    let mut current_core: usize = 999_999;
    let mut core_was_rebuilt: Option<usize> = None;
    let stage_size: usize = 32;
    #[cfg(feature = "rephase")]
    let mut sls_core = cdb.derefer(cdb::property::Tusize::NumClause);

    state.stm.initialize(stage_size);
    while 0 < asg.derefer(assign::property::Tusize::NumUnassignedVar) || asg.remains() {
        if !asg.remains() {
            let lit = vam.select_decision_literal();
            asg.assign_by_decision(lit);
        }
        let Err(cc) = propagate(vars, asg, vam, cdb) else {
            continue;
        };
        if asg.decision_level() == asg.root_level() {
            return Err(SolverError::RootLevelConflict);
        }
        vam.update_activity_tick();
        #[cfg(feature = "clause_rewarding")]
        cdb.update_activity_tick();
        if 1 < handle_conflict(vars, vam, asg, cdb, state, &cc)? {
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
            RESTART!(vars, asg, vam, cdb, state);
            vam.select_rephasing_target();
            clear_asserted_literals(vars, asg, vam, cdb)?;

            #[cfg(feature = "trace_equivalency")]
            cdb.check_consistency(asg, "before simplify");

            dump_stage(asg, cdb, state, previous_stage);
            let next_stage: Option<bool> = state.stm.prepare_new_stage(num_learnt);
            let scale = state.stm.current_scale();
            let max_scale = state.stm.max_scale();
            if cfg!(feature = "reward_annealing") {
                let base = state.stm.current_stage() - state.stm.cycle_starting_stage();
                let decay_index: f64 = (20 + 2 * base) as f64;
                vam.update_activity_decay((decay_index - 1.0) / decay_index);
            }
            if let Some(new_segment) = next_stage {
                // a beginning of a new cycle
                {
                    state.exploration_rate_ema.update(1.0);
                    if cfg!(feature = "two_mode_reduction") {
                        cdb.reduce(
                            asg,
                            ReductionType::LBDonALL(
                                state.config.cls_rdc_lbd,
                                state.config.cls_rdc_rm2,
                            ),
                        );
                    }
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
                        } else if new_segment {
                            let n = cdb.derefer(cdb::property::Tusize::NumClause);
                            let steps = scale!(27_u32, current_core) * scale!(24_u32, n) / ent;
                            let mut assignment = asg.best_phases_ref(Some(false));
                            sls!(assignment, steps);
                        }
                    }
                    asg.select_rephasing_target();
                }
                // if cfg!(feature = "clause_vivification") {
                //     cdb.vivify(asg, state)?;
                // }
                if new_segment {
                    {
                        let base = state.stm.current_segment();
                        let decay_index: f64 = (20 + 2 * base) as f64;
                        vam.update_activity_decay((decay_index - 1.0) / decay_index);
                    }
                    // if cfg!(feature = "clause_elimination") {
                    //     let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
                    //     state.flush("clause subsumption, ");
                    //     elim.simplify(asg, cdb, state, false)?;
                    //     asg.eliminated.append(elim.eliminated_lits());
                    //     state[Stat::Simplify] += 1;
                    //     state[Stat::SubsumedClause] = elim.num_subsumed;
                    // }
                    if cfg!(feature = "dynamic_restart_threshold") {
                        state.restart.set_segment_parameters(max_scale);
                    }
                }
            } else {
                {
                    if cfg!(feature = "two_mode_reduction") {
                        cdb.reduce(
                            asg,
                            ReductionType::RASonADD(
                                state.stm.num_reducible(state.config.cls_rdc_rm1),
                            ),
                        );
                    }
                }
            }
            {
                if !cfg!(feature = "two_mode_reduction") {
                    cdb.reduce(
                        asg,
                        ReductionType::RASonADD(state.stm.num_reducible(state.config.cls_rdc_rm1)),
                    );
                }
            }
            state.progress(asg, cdb);
            asg.handle(SolverEvent::Stage(scale));
            state.restart.set_stage_parameters(scale);
            previous_stage = next_stage;
        } else if state.restart.restart(
            cdb.refer(cdb::property::TEma::LBD),
            cdb.refer(cdb::property::TEma::Entanglement),
        ) {
            RESTART!(vars, asg, vam, cdb, state);
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
fn dump_stage<'a>(
    asg: &AssignStack<'a>,
    cdb: &mut ClauseDB<'a>,
    state: &mut State<'a>,
    shift: Option<bool>,
) {
    let active = true; // state.rst.enable;
    let cycle = state.stm.current_cycle();
    let span = state.stm.current_span();
    let stage = state.stm.current_stage();
    let segment = state.stm.current_segment();
    let cpr = asg.refer(assign::property::TEma::ConflictPerRestart).get();
    let vdr = 0.0; // asg.derefer(assign::property::Tf64::VarDecayRate);
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

#[cfg(feature = "boundary_check")]
#[allow(dead_code)]
fn check(asg: &mut AssignStack<'a>, cdb: &mut ClauseDB, all: bool, message: &str) {
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
            last_lit.var.propagated_at,
            last_lit.var.level,
            i32::from(last_lit),
            format!("{:?}", last_lit.assigned()),
            format!("{}", last_lit.var.reason),
        );
        panic!();
    }
}

#[cfg(feature = "support_user_assumption")]
// Build a conflict clause caused by *assumed* literals UNDER ROOT_LEVEL.
// So we use zero instead of root_level sometimes in this function.
fn analyze_final(asg: &mut AssignStack<'a>, state: &mut State, c: &Clause) {
    let mut seen = vec![false; asg.num_vars + 1];
    state.conflicts.clear();
    if asg.decision_level() == 0 {
        return;
    }
    // ??
    // for l in &c.lits {
    //     let vi = l.var.id;
    //     if asg.root_level < asg.level(vi) {
    //         asg.var_mut(vi).turn_on(Flag::CA_SEEN);
    //     }
    // }
    // FIXME: asg.stack_range().rev() is correct.
    for l in asg.stack_range(0..asg.len_upto(asg.root_level)) {
        let vi = l.var.id;
        if seen[vi] {
            if let AssignReason::Decision(_) = asg.reason(vi) {
                state.conflicts.push(!*l);
            } else {
                for l in &c[(c.len() != 2) as usize..] {
                    let vj = l.var.id;
                    if 0 < asg.level(vj) {
                        seen[vj] = true;
                    }
                }
            }
        }
        seen[vi] = false;
    }
}

/// inject assignments for eliminated vars.
#[allow(unused_variables)]
fn extend_model<'a>(vars: &mut [Var], cdb: &mut impl ClauseDBIF<'a>) -> Vec<Option<bool>> {
    // let lits = &self.eliminated;
    let lits = vars
        .iter()
        .skip(1)
        .filter(|v| v.is(FlagVar::ELIMINATED))
        .map(|v| Lit::try_from(v).unwrap())
        .collect::<Vec<_>>();

    #[cfg(feature = "trace_elimination")]
    println!(
        "# extend_model\n - as i32: {:?}\n - as raw: {:?}",
        i32s(lits),
        lits.iter()
            .map(|l| {
                let i = i32::from(l);
                if i < 0 {
                    -2 * i
                } else {
                    2 * i + 1
                }
            })
            .collect::<Vec<_>>(),
    );
    let mut extended_model: Vec<Option<bool>> = self.assign_ref();
    if lits.is_empty() {
        return extended_model;
    }
    let mut i = lits.len();
    while 0 < i {
        i -= 1;
        let width = usize::from(lits[i]);
        debug_assert!(0 < width);
        debug_assert!(width <= i);
        let target_index = i - width;
        let last_lit_index = i - 1;
        let reason_literals = target_index + 1..=last_lit_index;
        i = target_index;
        debug_assert!(
            lits[reason_literals.clone()]
                .iter()
                .all(|l| extended_model[l.var.id].is_some()),
            "impossible: pseudo clause has unassigned literal(s)."
        );
        if lits[reason_literals.clone()]
            .iter()
            .all(|l| extended_model[l.var.id] == Some(!bool::from(*l)))
        {
            let l = lits[target_index];
            extended_model[l.var.id] = Some(l.possitive);
        } else if lits[reason_literals.clone()]
            .iter()
            .any(|l| extended_model[l.var.id] == Some(l.possitive))
        {
            continue;
        }
    }
    extended_model
}

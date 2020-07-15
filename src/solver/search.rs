//! Conflict-Driven Clause Learning Search engine
use {
    super::{
        conflict::handle_conflict,
        restart::{RestartIF, Restarter, RestarterModule},
        vivify::vivify,
        Certificate, Solver, SolverEvent, SolverResult,
    },
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarRewardIF, VarSelectIF},
        cdb::{ClauseDB, ClauseDBIF},
        processor::{EliminateIF, Eliminator},
        state::{Stat, State, StateIF},
        types::*,
    },
};

/// API for SAT solver like `build`, `solve` and so on.
pub trait SolveIF {
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solve(&mut self) -> SolverResult;
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
        asg.num_solved_vars = asg.stack_len();
        state.progress_header();
        state.progress(asg, cdb, elim, rst, Some("preprocessing stage"));
        if 0 < asg.stack_len() {
            cdb.eliminate_satisfied_clauses(asg, elim, false);
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
                    // We can't call `asg.assign_at_rootlevel(l)` even if p or m == 0.
                    // This means we can't pick `!l`.
                    // This becomes a problem in the case of incremental solving.
                    #[cfg(not(feature = "incremental_solver"))]
                    {
                        if m == 0 {
                            let l = Lit::from_assign(vi, true);
                            if asg.assign_at_rootlevel(l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        } else if p == 0 {
                            let l = Lit::from_assign(vi, false);
                            if asg.assign_at_rootlevel(l).is_err() {
                                return Ok(Certificate::UNSAT);
                            }
                        }
                    }
                    asg.var_mut(vi).set(Flag::PHASE, m < p);
                    elim.enqueue_var(asg, vi, false);
                }
            }
            #[cfg(feature = "temp_order")]
            asg.force_select_iter(Some(elim.sorted_iterator()));
            //
            //## Run eliminator
            //
            if USE_PRE_PROCESSING_ELIMINATOR {
                state.flush("simplifying...");
                if elim.simplify(asg, cdb, state).is_err() {
                    // Why inconsistent? Because the CNF contains a conflict, not an error!
                    // Or out of memory.
                    state.progress(asg, cdb, elim, rst, None);
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
                asg.rebuild_order();
            }
            elim.stop(asg, cdb);
        }

        //
        //## Search
        //
        state.progress(asg, cdb, elim, rst, None);
        let answer = search(asg, cdb, elim, rst, state);
        state.progress(asg, cdb, elim, rst, None);
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
    let mut a_decision_was_made = false;
    let mut num_assigned = asg.num_solved_vars;
    let mut nrestart = 0; // #restarts in the current mode
    let mut restart_waiting = 0; // should be a function taking `nrestart`
    let mut wait_peak = 0;
    rst.update(RestarterModule::Luby, 0);
    state.stabilize = false;
    state.restart_absorption = 0;

    loop {
        asg.reward_update();
        let ci = asg.propagate(cdb);
        if ci.is_none() {
            if asg.num_vars <= asg.stack_len() + asg.num_eliminated_vars {
                return Ok(true);
            }

            //
            //## DYNAMIC FORCING RESTART based on LBD values, updated by conflict
            //
            state.last_asg = asg.stack_len();
            if rst.force_restart() {
                let na = asg.var_stats().1;

                if num_assigned < na {
                    num_assigned = na;
                    // reset incremental deep search
                    state.restart_absorption = 0;
                    restart_waiting = 0;
                }

                restart_waiting += 1;
                if state.restart_absorption <= restart_waiting {
                    // time to restart and incrment parameters
                    restart_waiting = 0;
                    nrestart += 1;
                    state.restart_absorption = if state.stabilize {
                        int_floor(nrestart) // rst.exports().4
                    } else {
                        0 // int_floor(nrestart)
                    };
                }
                if wait_peak < nrestart {
                    wait_peak = nrestart;
                }
                if restart_waiting == 0 {
                    asg.cancel_until(asg.root_level);
                }
                #[cfg(feature = "temp_order")]
                asg.force_select_iter(None);
            } else {
                restart_waiting = 0;
            }
        } else {
            if asg.decision_level() == asg.root_level {
                analyze_final(asg, state, &cdb[ci]);
                return Ok(false);
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
            if state.stabilize {
                asg.force_rephase();
            }
            if state.config.viv_interval <= state.to_vivify && state.config.use_vivify() {
                state.to_vivify = 0;
                if !cdb.use_chan_seok && vivify(asg, cdb, elim, state).is_err() {
                    return Err(SolverError::UndescribedError);
                }
            }
            // `elim.to_simplify` is increased much in particular when vars are solved or
            // learnts are small. We don't need to count the number of solved vars.
            if state.config.ip_interval <= elim.to_simplify as usize {
                elim.to_simplify = 0.0;
                if elim.enable {
                    elim.activate();
                }
                elim.simplify(asg, cdb, state)?;
                if state.config.use_vivify() && cdb.use_chan_seok {
                    state.to_vivify = 0;
                    if vivify(asg, cdb, elim, state).is_err() {
                        return Err(SolverError::UndescribedError);
                    }
                }
            }
            // By simplification, we may get further solutions.
            if asg.num_solved_vars < asg.stack_len() {
                rst.update(RestarterModule::Reset, 0);
                asg.num_solved_vars = asg.stack_len();
            }
        }
        let na = asg.best_assigned(Flag::PHASE);
        if num_assigned < na {
            num_assigned = na;

            // reset incremental deep search
            nrestart = 0;
            state.restart_absorption = 0;

            state.flush("");
            state.flush(format!("unreachable: {}", asg.num_vars - num_assigned));
        }
        if !asg.remains() {
            if state.config.use_stabilize() && state.stabilize != rst.stabilizing() {
                state.stabilize = !state.stabilize;
                nrestart = 0;
                state.restart_absorption = 0;
                rst.handle(SolverEvent::Stabilize(state.stabilize));
            }
            let lit = asg.select_decision_literal(&state.phase_select);
            asg.assign_by_decision(lit);
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
        state.select_strategy(asg, cdb);
        if elim.exports().0 < 2 {
            state.config.ip_interval = state.config.ip_interval.min(elim.to_simplify as usize);
        }
    }
    #[cfg(feature = "boundary_check")]
    assert!(state.strategy.1 != asg_num_conflict || 0 == asg.decision_level());
    asg.handle(SolverEvent::Adapt(state.strategy, asg_num_conflict));
    cdb.handle(SolverEvent::Adapt(state.strategy, asg_num_conflict));
    rst.handle(SolverEvent::Adapt(state.strategy, asg_num_conflict));
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

// a very slow floor function mapping on int
fn int_floor(n: usize) -> usize {
    const PRIMES: [usize; 168] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
        283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
        509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
        751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
    ];
    fn int_sqrt(n: usize) -> usize {
        (n as f64).sqrt() as usize
    }
    for i in PRIMES.iter() {
        if n == *i {
            return 0;
        }
        if n % i == 0 {
            return int_sqrt(i - 2);
        }
    }
    0
}

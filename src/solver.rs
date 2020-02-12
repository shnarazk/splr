/// Crate 'solver' provides the top-level API as a SAT solver.
use {
    crate::{
        clause::{Clause, ClauseDB, ClauseDBIF, ClauseIF, ClauseId},
        config::Config,
        eliminator::{Eliminator, EliminatorIF},
        propagator::{AssignStack, PropagatorIF, VarSelectionIF},
        restart::RestartIF,
        state::{Stat, State, StateIF},
        types::*,
        var::{VarDB, VarDBIF, VarRewardIF, LBDIF},
    },
    std::{convert::TryFrom, io::BufRead},
};

/// API for SAT solver like `build`, `solve` and so on.
pub trait SatSolverIF {
    /// make a solver and load a CNF into it.
    ///
    /// # Errors
    ///
    /// IO error by failing to load a CNF file.
    fn build(config: &Config) -> Result<Solver, SolverError>;
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solve(&mut self) -> SolverResult;
    /// add a vector of `Lit` as a clause to the solver.
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

/// Normal results returned by Solver.
#[derive(Debug, PartialEq)]
pub enum Certificate {
    SAT(Vec<i32>),
    UNSAT,
}

/// The return type of `Solver::solve`.
/// This captures the following three cases:
/// * `Certificate::SAT` -- solved with a satisfiable assignment set,
/// * `Certificate::UNSAT` -- proved that it's an unsatisfiable problem, and
/// * `SolverException::*` -- caused by a bug
pub type SolverResult = Result<Certificate, SolverError>;

/// SAT solver consisting of 5 sub modules.
#[derive(Debug)]
pub struct Solver {
    pub asgs: AssignStack, // Assignment
    pub cdb: ClauseDB,     // Clauses
    pub elim: Eliminator,  // Clause/Variable Elimination
    pub state: State,      // misc data
    pub vdb: VarDB,        // Variables
}

impl Default for Solver {
    fn default() -> Solver {
        Solver {
            asgs: AssignStack::default(),
            cdb: ClauseDB::default(),
            elim: Eliminator::default(),
            state: State::default(),
            vdb: VarDB::default(),
        }
    }
}

impl Instantiate for Solver {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Solver {
        Solver {
            asgs: AssignStack::instantiate(config, cnf),
            cdb: ClauseDB::instantiate(config, cnf),
            elim: Eliminator::instantiate(config, cnf),
            state: State::instantiate(config, cnf),
            vdb: VarDB::instantiate(config, cnf),
        }
    }
}

impl SatSolverIF for Solver {
    /// # Examples
    ///
    /// ```
    /// use splr::config::Config;
    /// use splr::solver::{Certificate, SatSolverIF, Solver};
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
            ref mut asgs,
            ref mut cdb,
            ref mut elim,
            ref mut state,
            ref mut vdb,
        } = self;
        if cdb.check_size().is_err() {
            return Err(SolverError::OutOfMemory);
        }
        // NOTE: splr doesn't deal with assumptions.
        // s.root_level = 0;
        state.num_solved_vars = asgs.len();
        state.progress_header();
        state.progress(cdb, vdb, Some("initialization phase"));
        state.flush("loading...");
        let use_pre_processor = true;
        let use_pre_processing_eliminator = true;
        if use_pre_processor {
            state.flush("phasing...");
            elim.activate();
            elim.prepare(cdb, vdb, true);
            // run simple preprocessor
            for vi in 1..vdb.len() {
                let v = &mut vdb[vi];
                if v.assign.is_some() {
                    continue;
                }
                match (v.pos_occurs.len(), v.neg_occurs.len()) {
                    (_, 0) => {
                        let l = Lit::from_assign(vi, true);
                        if asgs.assign_at_rootlevel(vdb, l).is_err() {
                            return Ok(Certificate::UNSAT);
                        }
                    }
                    (0, _) => {
                        let l = Lit::from_assign(vi, false);
                        if asgs.assign_at_rootlevel(vdb, l).is_err() {
                            return Ok(Certificate::UNSAT);
                        }
                    }
                    (p, m) => {
                        v.phase = m < p;
                        elim.enqueue_var(vdb, vi, false);
                    }
                }
            }
            if !elim.enable || !use_pre_processing_eliminator {
                elim.stop(cdb, vdb);
            }
        }
        if elim.enable && use_pre_processing_eliminator {
            state.flush("simplifying...");
            // if 20_000_000 < state.target.num_of_clauses {
            //     state.elim_eliminate_grow_limit = 0;
            //     state.elim_eliminate_loop_limit = 1_000_000;
            //     state.elim_subsume_loop_limit = 2_000_000;
            // }
            if cdb.simplify(asgs, elim, state, vdb).is_err() {
                // Why inconsistent? Because the CNF contains a conflict, not an error!
                // Or out of memory.
                state.progress(cdb, vdb, None);
                if cdb.check_size().is_err() {
                    return Err(SolverError::OutOfMemory);
                }
                return Ok(Certificate::UNSAT);
            }
            for v in &mut vdb[1..] {
                if v.assign.is_some() || v.is(Flag::ELIMINATED) {
                    continue;
                }
                match (v.pos_occurs.len(), v.neg_occurs.len()) {
                    (_, 0) => (),
                    (0, _) => (),
                    (p, m) if m * 10 < p => v.phase = true,
                    (p, m) if p * 10 < m => v.phase = false,
                    _ => (),
                }
            }
        }
        vdb.initialize_reward(elim.sorted_iterator());
        asgs.rebuild_order(vdb);
        state.progress(cdb, vdb, None);
        match search(asgs, cdb, elim, state, vdb) {
            Ok(true) => {
                state.progress(cdb, vdb, None);
                let mut result = Vec::new();
                for (vi, v) in vdb[0..].iter().enumerate().take(state.num_vars + 1).skip(1) {
                    match v.assign {
                        Some(true) => result.push(vi as i32),
                        Some(false) => result.push(0 - vi as i32),
                        _ => result.push(0),
                    }
                }
                elim.extend_model(&mut result);
                asgs.cancel_until(vdb, 0);
                Ok(Certificate::SAT(result))
            }
            Ok(false) => {
                state.progress(cdb, vdb, None);
                asgs.cancel_until(vdb, 0);
                Ok(Certificate::UNSAT)
            }
            Err(_) => {
                asgs.cancel_until(vdb, 0);
                state.progress(cdb, vdb, None);
                if cdb.check_size().is_err() {
                    Err(SolverError::OutOfMemory)
                } else if state.is_timeout() {
                    Err(SolverError::TimeOut)
                } else {
                    Err(SolverError::Inconsistent)
                }
            }
        }
    }
    /// # Examples
    ///
    /// ```
    /// use splr::config::Config;
    /// use splr::solver::{SatSolverIF, Solver};
    ///
    /// let config = Config::from("tests/sample.cnf");
    /// assert!(Solver::build(&config).is_ok());
    ///```
    fn build(config: &Config) -> Result<Solver, SolverError> {
        let CNFReader { cnf, mut reader } = CNFReader::try_from(&config.cnf_filename)?;
        let mut buf = String::new();
        let mut s: Solver = Solver::instantiate(config, &cnf);
        loop {
            buf.clear();
            match reader.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_) => {
                    if buf.starts_with('c') {
                        continue;
                    }
                    let iter = buf.split_whitespace();
                    let mut v: Vec<Lit> = Vec::new();
                    for s in iter {
                        match s.parse::<i32>() {
                            Ok(0) => break,
                            Ok(val) => v.push(Lit::from(val)),
                            Err(_) => (),
                        }
                    }
                    if !v.is_empty() && s.add_unchecked_clause(&mut v).is_none() {
                        return Err(SolverError::Inconsistent);
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(s.vdb.len() - 1, cnf.num_of_variables);
        s.state[Stat::NumBin] = s.cdb[1..].iter().filter(|c| c.len() == 2).count();
        match s.vdb.len() {
            l if 1_000_000 < l => s.vdb.activity_step *= 0.1,
            l if 100_000 < l => s.vdb.activity_step *= 0.5,
            _ => (),
        }
        Ok(s)
    }
    // renamed from clause_new
    fn add_unchecked_clause(&mut self, lits: &mut Vec<Lit>) -> Option<ClauseId> {
        let Solver {
            ref mut asgs,
            ref mut cdb,
            ref mut elim,
            ref mut vdb,
            ..
        } = self;
        debug_assert!(asgs.level() == 0);
        if lits.iter().any(|l| vdb.assigned(*l).is_some()) {
            cdb.certificate_add(lits);
        }
        lits.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means tautology.
        for i in 0..lits.len() {
            let li = lits[i];
            let sat = vdb.assigned(li);
            if sat == Some(true) || !li == l_ {
                return Some(ClauseId::default());
            } else if sat != Some(false) && li != l_ {
                lits[j] = li;
                j += 1;
                l_ = li;
            }
        }
        lits.truncate(j);
        match lits.len() {
            0 => None, // Empty clause is UNSAT.
            1 => {
                if asgs.assign_at_rootlevel(vdb, lits[0]).is_ok() {
                    Some(ClauseId::default())
                } else {
                    None
                }
            }
            _ => {
                let cid = cdb.new_clause(lits, 0, false);
                elim.add_cid_occur(vdb, cid, &mut cdb[cid], true);
                Some(cid)
            }
        }
    }
}

/// main loop; returns `true` for SAT, `false` for UNSAT.
fn search(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vdb: &mut VarDB,
) -> Result<bool, SolverError> {
    let mut a_decision_was_made = false;
    if state.rst.luby.active {
        state.rst.luby.update(0);
    }
    loop {
        vdb.reward_update();
        let ci = asgs.propagate(cdb, vdb);
        state[Stat::Propagation] += 1;
        if ci == ClauseId::default() {
            if state.num_vars <= asgs.len() + state.num_eliminated_vars {
                return Ok(true);
            }
            // DYNAMIC FORCING RESTART based on LBD values, updated by conflict
            state.last_asg = asgs.len();
            if state.rst.force_restart() {
                state[Stat::Restart] += 1;
                asgs.cancel_until(vdb, state.root_level);
            } else if asgs.level() == 0 {
                if cdb.simplify(asgs, elim, state, vdb).is_err() {
                    debug_assert!(false, "interal error by simplify");
                    return Err(SolverError::Inconsistent);
                }
                state.num_solved_vars = asgs.len();
            }
            if !asgs.remains() {
                let vi = asgs.select_var(vdb);
                let p = vdb[vi].phase;
                asgs.assign_by_decision(vdb, Lit::from_assign(vi, p));
                state[Stat::Decision] += 1;
                a_decision_was_made = true;
            }
        } else {
            state[Stat::Conflict] += 1;
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state[Stat::NoDecisionConflict] += 1;
            }
            if asgs.level() == state.root_level {
                analyze_final(asgs, state, vdb, &cdb[ci]);
                return Ok(false);
            }
            /// For Chronological Backtracking
            if cdb[ci].lits.iter().all(| l | vdb[*l].level == 0) {
                return Ok(false);
            }
            handle_conflict_path(asgs, cdb, elim, state, vdb, ci)?;
        }
    }
}

fn handle_conflict_path(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vdb: &mut VarDB,
    ci: ClauseId,
) -> MaybeInconsistent {
    let ncnfl = state[Stat::Conflict]; // total number
    state.rst.after_restart += 1;
    // DYNAMIC BLOCKING RESTART based on ASG, updated on conflict path
    // If we can settle this conflict w/o restart, solver will get a big progress.
    if 0 < state.last_asg {
        state.rst.asg.update(asgs.len());
        state.last_asg = 0;
    }
    if state.rst.block_restart() {
        state[Stat::BlockRestart] += 1;
    }
    let cl = asgs.level();
    let use_chrono_bt = true;
    if use_chrono_bt {
        let c = &cdb[ci];
        let ls_max = c.lits.iter().map(|l| vdb[*l].level == cl).count();
        if 1 == ls_max {
            let snd_l = c
                .lits
                .iter()
                .map(|l| vdb[*l].level)
                .filter(|l| *l != cl)
                .max()
                .unwrap_or(0);
            // If the conflicting clause contains one literallfrom the maximal
            // decision level, we let BCP propagating that literal at the second
            // highest decision level in conflicting cls.
            asgs.cancel_until(vdb, snd_l);
            return Ok(());
        } else {
            let lv = c.lits.iter().map(|l| vdb[*l].level).max().unwrap_or(0);
            asgs.cancel_until(vdb, lv); // this changes the decision level `cl`.
        }
    }
    let cl = asgs.level();
    let bl = conflict_analyze(asgs, cdb, state, vdb, ci).max(state.root_level);
//    if state.new_learnt.is_empty() {
//        return Err(SolverError::StateUNSAT);
//    }
    // vdb.bump_vars(asgs, cdb, ci);
    let chrono_bt = 10_000 < ncnfl && 100 < cl - bl;
    let new_learnt = &mut state.new_learnt;
    let l0 = new_learnt[0];
    let al = if chrono_bt {
        new_learnt[1..]
            .iter()
            .map(|l| vdb[*l].level)
            .max()
            .unwrap_or(0)
    } else {
        bl
    };
    let learnt_len = new_learnt.len();
    if learnt_len == 1 {
        // dump to certified even if it's a literal.
        cdb.certificate_add(new_learnt);
        // force to use chrono_bt
        asgs.cancel_until(vdb, cl - 1);
        asgs.assign_by_implication(vdb, l0, ClauseId::default(), al);
        state.num_solved_vars += 1;
    } else {
        {
            // Reason-Side Rewarding
            let mut bumped = Vec::new();
            for lit in new_learnt.iter() {
                for l in &cdb[vdb[lit.vi()].reason].lits {
                    if !bumped.contains(l) {
                        vdb.reward_at_analysis(l.vi());
                        bumped.push(*l);
                    }
                }
            }
        }
        if chrono_bt {
            asgs.cancel_until(vdb, cl - 1);
        } else {
            asgs.cancel_until(vdb, bl);
        }
        let lbd = vdb.compute_lbd(&new_learnt);
        let cid = cdb.attach(state, vdb, lbd);
        elim.add_cid_occur(vdb, cid, &mut cdb[cid], true);
        state.c_lvl.update(cl as f64);
        state.b_lvl.update(bl as f64);
        if lbd <= 2 {
            state[Stat::NumLBD2] += 1;
        }
        if learnt_len == 2 {
            state[Stat::NumBin] += 1;
            state[Stat::NumBinLearnt] += 1;
        }
        if chrono_bt {
            asgs.assign_by_implication(vdb, l0, cid, al);
        } else {
            asgs.assign_by_implication(vdb, l0, cid, bl);
        }
        state.rst.lbd.update(lbd);
        state[Stat::SumLBD] += lbd;
        state[Stat::Learnt] += 1;
    }
    cdb.scale_activity();
    if 0 < state.config.dump_interval && ncnfl % state.config.dump_interval == 0 {
        state.development.push((
            ncnfl,
            (state.num_solved_vars + state.num_eliminated_vars) as f64
                / state.target.num_of_variables as f64,
            state[Stat::Restart] as f64,
            state[Stat::BlockRestart] as f64,
            state.rst.asg.trend().min(10.0),
            state.rst.lbd.trend().min(10.0),
        ));
    }
    if ncnfl % state.reflection_interval == 0 {
        adapt_parameters(asgs, cdb, elim, state, vdb, ncnfl)?;
        if let Some(p) = state.elapsed() {
            if 1.0 <= p {
                return Err(SolverError::TimeOut);
            } else if state.default_rewarding && 0.5 <= p {
                // force the final stage of rewarding to switch to 'deep search' mode
                state.default_rewarding = false;
                vdb.shift_reward_mode();
            }
        } else {
            return Err(SolverError::UndescribedError);
        }
    }
    if ((state.use_chan_seok && !cdb.glureduce && cdb.first_reduction < cdb.num_learnt)
        || (cdb.glureduce && cdb.cur_restart * cdb.next_reduction <= state[Stat::Conflict]))
        && 0 < cdb.num_learnt
    {
        cdb.cur_restart = ((ncnfl as f64) / (cdb.next_reduction as f64)) as usize + 1;
        cdb.reduce(state, vdb);
    }
    Ok(())
}

fn adapt_parameters(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vdb: &mut VarDB,
    nconflict: usize,
) -> MaybeInconsistent {
    let switch = 10 * state.reflection_interval;
    state.check_stagnation();
    if nconflict == switch {
        state.flush("exhaustive eliminator activated...");
        asgs.cancel_until(vdb, 0);
        state.adapt_strategy(cdb);
        if elim.enable {
            elim.activate();
            cdb.simplify(asgs, elim, state, vdb)?;
        }
    }
    state[Stat::SolvedRecord] = state.num_solved_vars;
    if !state.config.without_deep_search {
        if state.stagnated {
            state.rst.restart_step = state.reflection_interval;
            state.rst.next_restart += state.reflection_interval;
        } else {
            state.rst.restart_step = state.config.restart_step;
        }
    }
    state.progress(cdb, vdb, None);
    Ok(())
}

fn conflict_analyze(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    vdb: &mut VarDB,
    confl: ClauseId,
) -> usize {
    let learnt = &mut state.new_learnt;
    learnt.clear();
    learnt.push(NULL_LIT);
    let dl = asgs.level();
    let mut cid = confl;
    let mut p = NULL_LIT;
    let mut ti = asgs.len() - 1; // trail index
    let mut path_cnt = 0;
    let lbd_bound = cdb.co_lbd_bound;
    loop {
        // println!("analyze {}", p.int());
        debug_assert_ne!(cid, ClauseId::default());
        if cdb[cid].is(Flag::LEARNT) {
            cdb.bump_activity(cid, ());
            let c = &mut cdb[cid];
            debug_assert!(!c.is(Flag::DEAD));
            if 2 < c.rank {
                let nlevels = vdb.compute_lbd(&c.lits);
                if nlevels + 1 < c.rank {
                    // if c.rank <= cdb.lbd_frozen_clause {
                    //     c.turn_on(Flag::JUST_USED);
                    // }
                    if state.use_chan_seok && nlevels < lbd_bound {
                        c.turn_off(Flag::LEARNT);
                        cdb.num_learnt -= 1;
                    } else {
                        c.rank = nlevels;
                    }
                }
            }
        }
        let c = &cdb[cid];
        // println!("- handle {}", cid.fmt());
        for q in &c[(p != NULL_LIT) as usize..] {
            let vi = q.vi();
            if !vdb[vi].is(Flag::CA_SEEN) {
                vdb.reward_at_analysis(vi);
                let v = &mut vdb[vi];
                if 0 == v.level {
                    continue;
                }
                debug_assert!(!v.is(Flag::ELIMINATED));
                debug_assert!(v.assign.is_some());
                v.turn_on(Flag::CA_SEEN);
                if dl <= v.level {
                    // println!("- flag for {} which level is {}", q.int(), lvl);
                    path_cnt += 1;
                } else {
                    // println!("- push {} to learnt, which level is {}", q.int(), lvl);
                    learnt.push(*q);
                }
            } else {
                // if !v.is(Flag::CA_SEEN) {
                //     println!("- ignore {} because it was flagged", q.int());
                // } else {
                //     println!("- ignore {} because its level is {}", q.int(), lvl);
                // }
            }
        }
        // set the index of the next literal to ti
        while !vdb[asgs.trail[ti].vi()].is(Flag::CA_SEEN) {
            // println!("- skip {} because it isn't flagged", asgs.trail[ti].int());
//            if ti == 0 && path_cnt == 0 {
//                learnt.remove(0);
//                return simplify_learnt(asgs, cdb, state, vdb);
//            }
//            assert!(0 < ti,
//                    format!("got:{}, dl:{}, path_cnt: {}",
//                            learnt.len(),
//                            asgs.level(),
//                            path_cnt,
//                    ),
//            );
            ti -= 1;
        }
        p = asgs.trail[ti];
        let next_vi = p.vi();
        cid = vdb[next_vi].reason;
        // println!("- move to flagged {}, which reason is {}; num path: {}",
        //          next_vi, path_cnt - 1, cid.fmt());
        vdb[next_vi].turn_off(Flag::CA_SEEN);
        // since the trail can contain a literal which level is under `dl` after
        // the `dl`-th thdecision var, we must skip it.
        if vdb[next_vi].level == dl {
            path_cnt -= 1;
        }
        if path_cnt == 0 {
            break;
        }
        debug_assert!(0 < ti);
        ti -= 1;
        debug_assert_ne!(cid, ClauseId::default());
    }
    if learnt.len() == 2 && learnt[1] == !p {
        learnt.truncate(1);
    }
    // assert!(learnt.iter().all(| l | *l != !p));
    learnt[0] = !p;
    // assert_eq!(vdb[p].level, asgs.level());
    // println!("- appending {}, the result is {:?}", learnt[0].int(), vec2int(learnt));
    simplify_learnt(asgs, cdb, state, vdb)
}

fn simplify_learnt(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    vdb: &mut VarDB,
) -> usize {
    let State {
        ref mut new_learnt, ..
    } = state;
    // let dl = asgs.level();
//    if new_learnt.is_empty() {
//        return 0;
//    }
    let mut to_clear: Vec<Lit> = vec![new_learnt[0]];
    let mut levels = vec![false; asgs.level() + 1];
    for l in &new_learnt[1..] {
        to_clear.push(*l);
        levels[vdb[l.vi()].level] = true;
    }
    new_learnt.retain(|l| {
        vdb[l.vi()].reason == ClauseId::default()
            || !redundant_lit(cdb, vdb, *l, &mut to_clear, &levels)
    });
    let len = new_learnt.len();
    if 2 < len && len < 30 {
        vdb.minimize_with_bi_clauses(cdb, new_learnt);
    }
    // find correct backtrack level from remaining literals
    let mut level_to_return = 0;
    if 1 < new_learnt.len() {
        let mut max_i = 1;
        level_to_return = vdb[new_learnt[max_i].vi()].level;
        for (i, l) in new_learnt.iter().enumerate().skip(2) {
            let lv = vdb[l.vi()].level;
            if level_to_return < lv {
                level_to_return = lv;
                max_i = i;
            }
        }
        new_learnt.swap(1, max_i);
    }
    for l in &to_clear {
        vdb[l.vi()].turn_off(Flag::CA_SEEN);
    }
    level_to_return
}

fn redundant_lit(
    cdb: &mut ClauseDB,
    vdb: &mut VarDB,
    l: Lit,
    clear: &mut Vec<Lit>,
    levels: &[bool],
) -> bool {
    let mut stack = Vec::new();
    stack.push(l);
    let top = clear.len();
    while let Some(sl) = stack.pop() {
        let cid = vdb[sl.vi()].reason;
        let c = &mut cdb[cid];
        for q in &(*c)[1..] {
            let vi = q.vi();
            let v = &vdb[vi];
            let lv = v.level;
            if 0 < lv && !v.is(Flag::CA_SEEN) {
                if v.reason != ClauseId::default() && levels[lv as usize] {
                    vdb[vi].turn_on(Flag::CA_SEEN);
                    stack.push(*q);
                    clear.push(*q);
                } else {
                    for l in &clear[top..] {
                        vdb[l.vi()].turn_off(Flag::CA_SEEN);
                    }
                    clear.truncate(top);
                    return false;
                }
            }
        }
    }
    true
}

fn analyze_final(asgs: &AssignStack, state: &mut State, vdb: &mut VarDB, c: &Clause) {
    let mut seen = vec![false; state.num_vars + 1];
    state.conflicts.clear();
    if asgs.level() == 0 {
        return;
    }
    for l in &c.lits {
        let vi = l.vi();
        if 0 < vdb[vi].level {
            vdb[vi].turn_on(Flag::CA_SEEN);
        }
    }
    let end = if asgs.level() <= state.root_level {
        asgs.len()
    } else {
        asgs.len_upto(state.root_level)
    };
    for l in &asgs.trail[asgs.len_upto(0)..end] {
        let vi = l.vi();
        if seen[vi] {
            if vdb[vi].reason == ClauseId::default() {
                state.conflicts.push(!*l);
            } else {
                for l in &c[(c.len() != 2) as usize..] {
                    let vi = l.vi();
                    if 0 < vdb[vi].level {
                        seen[vi] = true;
                    }
                }
            }
        }
        seen[vi] = false;
    }
}

#[cfg(test)]
mod tests {
    use {super::*, std::path::PathBuf};
    #[test]
    fn test_solver() {
        let mut config = Config::default();
        config.cnf_filename = PathBuf::from("tests/sample.cnf");
        if let Ok(s) = Solver::build(&config) {
            assert_eq!(s.state.num_vars, 250);
            assert_eq!(s.state.num_unsolved_vars(), 250);
        } else {
            panic!("failed to build a solver for tests/sample.cnf");
        }
    }
}

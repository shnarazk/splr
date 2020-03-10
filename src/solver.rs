/// Crate 'solver' provides the top-level API as a SAT solver.
use {
    crate::{
        clause::{Clause, ClauseDB, ClauseDBIF, ClauseIF, ClauseId},
        config::Config,
        eliminator::{Eliminator, EliminatorIF, EliminatorStatIF},
        propagator::{AssignStack, PropagatorIF, VarSelectionIF},
        restarter::{Restarter, RestartIF},
        state::{Stat, State, StateIF},
        types::*,
        var::{VarDB, VarDBIF, VarRewardIF, LBDIF},
    },
    std::{convert::TryFrom, io::BufRead, slice::Iter},
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
    pub asgs: AssignStack,      // Assignment
    pub cdb: ClauseDB,          // Clauses
    pub elim: Eliminator,       // Clause/Variable Elimination
    pub rst: Restarter,         // restart module
    pub state: State,           // misc data
    pub vdb: VarDB,             // Variables
}

impl Default for Solver {
    fn default() -> Solver {
        Solver {
            asgs: AssignStack::default(),
            cdb: ClauseDB::default(),
            elim: Eliminator::default(),
            rst: Restarter::instantiate(&Config::default(), &CNFDescription::default()),
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
            rst: Restarter::instantiate(config, &cnf),
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
            ref mut rst,
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
        state.progress(cdb, rst, vdb, Some("initialization phase"));
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
                let w = &elim[vi];
                if v.assign.is_some() {
                    continue;
                }
                match w.stats() {
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
                        v.set(Flag::PHASE, m < p);
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
            if elim.simplify(asgs, cdb, state, vdb).is_err() {
                // Why inconsistent? Because the CNF contains a conflict, not an error!
                // Or out of memory.
                let q = state.config.quiet_mode;
                state.config.quiet_mode = false;
                state.progress(cdb, rst, vdb, None);
                state.config.quiet_mode = q;
                if cdb.check_size().is_err() {
                    return Err(SolverError::OutOfMemory);
                }
                return Ok(Certificate::UNSAT);
            }
            for v in &mut vdb[1..] {
                if v.assign.is_some() || v.is(Flag::ELIMINATED) {
                    continue;
                }
                match elim[v.index].stats() {
                    (_, 0) => (),
                    (0, _) => (),
                    (p, m) if m * 10 < p => v.turn_on(Flag::PHASE),
                    (p, m) if p * 10 < m => v.turn_off(Flag::PHASE),
                    _ => (),
                }
            }
        }
        vdb.initialize_reward(elim.sorted_iterator());
        asgs.rebuild_order(vdb);
        state.progress(cdb, rst, vdb, None);
        match search(asgs, cdb, elim, rst, state, vdb) {
            Ok(true) => {
                let q = state.config.quiet_mode;
                state.config.quiet_mode = false;
                state.progress(cdb, rst, vdb, None);
                state.config.quiet_mode = q;
                elim.extend_model(vdb);
                #[cfg(debug)]
                {
                    if let Some(cid) = cdb.validate(vdb, true) {
                        panic!(
                            "Level {} generated assignment({:?}) falsifies {}:{:?}",
                            asgs.level(),
                            cdb.validate(vdb, false).is_none(),
                            cid,
                            vdb.dump(&cdb[cid]),
                        );
                    }
                }
                if cdb.validate(vdb, true).is_some() {
                    return Err(SolverError::SolverBug);
                }
                let vals = vdb[1..]
                    .iter()
                    .map(|v| i32::from(Lit::from(v)))
                    .collect::<Vec<i32>>();
                asgs.cancel_until(vdb, 0);
                Ok(Certificate::SAT(vals))
            }
            Ok(false) | Err(SolverError::NullLearnt) => {
                state.progress(cdb, rst, vdb, None);
                asgs.cancel_until(vdb, 0);
                Ok(Certificate::UNSAT)
            }
            Err(e) => {
                asgs.cancel_until(vdb, 0);
                let q = state.config.quiet_mode;
                state.config.quiet_mode = false;
                state.progress(cdb, rst, vdb, None);
                state.config.quiet_mode = q;
                Err(e)
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
                Ok(_) if buf.starts_with('c') => continue,
                Ok(_) => {
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
        s.vdb.adapt_to(&s.state, false);
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
        if lits.is_empty() {
            return None;
        }
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

/// main loop; returns `Ok(true)` for SAT, `Ok(false)` for UNSAT.
#[inline]
fn search(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    vdb: &mut VarDB,
) -> Result<bool, SolverError> {
    let mut a_decision_was_made = false;
    if rst.luby.active {
        rst.luby.update(0);
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
            if rst.force_restart() {
                state[Stat::Restart] += 1;
                asgs.cancel_until(vdb, state.root_level);
            } else if asgs.level() == 0 {
                if elim.simplify(asgs, cdb, state, vdb).is_err() {
                    debug_assert!(false, "interal error by simplify");
                    return Err(SolverError::Inconsistent);
                }
                state.num_solved_vars = asgs.len();
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
            // handle a simple UNSAT case here.
            if cdb[ci].iter().all(|l| vdb[l].level == 0) {
                return Ok(false);
            }
            handle_conflict_path(asgs, cdb, elim, rst, state, vdb, ci)?;
        }
        if !asgs.remains() {
            let vi = asgs.select_var(vdb);
            let p = vdb[vi].is(Flag::PHASE);
            asgs.assign_by_decision(vdb, Lit::from_assign(vi, p));
            state[Stat::Decision] += 1;
            a_decision_was_made = true;
        }
    }
}

#[inline]
fn handle_conflict_path(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    vdb: &mut VarDB,
    ci: ClauseId,
) -> MaybeInconsistent {
    let ncnfl = state[Stat::Conflict]; // total number
    rst.after_restart += 1;
    // DYNAMIC BLOCKING RESTART based on ASG, updated on conflict path
    // If we can settle this conflict w/o restart, solver will get a big progress.
    if 0 < state.last_asg {
        rst.asg.update(asgs.len());
        state.last_asg = 0;
    }
    if rst.block_restart() {
        state[Stat::BlockRestart] += 1;
    }
    let cl = asgs.level();
    let mut use_chronobt = 1_000 < ncnfl && 0 < state.config.chronobt;
    if use_chronobt {
        let c = &cdb[ci];
        let lcnt = c.iter().filter(|l| vdb[*l].level == cl).count();
        if 1 == lcnt {
            debug_assert!(c.iter().any(|l| vdb[l].level == cl));
            let decision = *c.iter().find(|l| vdb[*l].level == cl).unwrap();
            let snd_l = c
                .iter()
                .map(|l| vdb[l].level)
                .filter(|l| *l != cl)
                .max()
                .unwrap_or(0);
            if 0 < snd_l {
                // If the conflicting clause contains one literallfrom the maximal
                // decision level, we let BCP propagating that literal at the second
                // highest decision level in conflicting cls.
                // PREMISE: 0 < snd_l
                asgs.cancel_until(vdb, snd_l - 1);
                debug_assert!(
                    asgs.iter().all(|l| l.vi() != decision.vi()),
                    format!("lcnt == 1: level {}, snd level {}", cl, snd_l)
                );
                asgs.assign_by_decision(vdb, decision);
                return Ok(());
            }
        }
        let lv = c.iter().map(|l| vdb[l].level).max().unwrap_or(0);
        // The following change the decision level which is stored to `cl`.
        asgs.cancel_until(vdb, lv);
    }
    // conflicting level
    let cl = asgs.level();
    debug_assert!(cdb[ci].iter().any(|l| vdb[l].level == cl));
    // backtrack level by analyze
    let bl_a = conflict_analyze(asgs, cdb, state, vdb, ci).max(state.root_level);
    if state.new_learnt.is_empty() {
        #[cfg(debug)]
        {
            println!(
                "empty learnt at {}({}) by {:?}",
                cl,
                vdb[asgs.decision_vi(cl)].reason == ClauseId::default(),
                vdb.dump(&cdb[ci]),
            );
        }
        return Err(SolverError::NullLearnt);
    }
    // vdb.bump_vars(asgs, cdb, ci);
    let new_learnt = &mut state.new_learnt;
    let l0 = new_learnt[0];
    // assert: 0 < cl, which was checked already by new_learnt.is_empty().

    // NCB places firstUIP on level bl, while CB does it on level cl.
    // Therefore the condition to use CB is: activity(firstUIP) < activity(v(bl)).
    // PREMISE: 0 < bl, because asgs.decision_vi accepts only non-zero values.
    use_chronobt &= bl_a == 0
        || state.config.chronobt + bl_a <= cl
        || vdb.activity(l0.vi()) < vdb.activity(asgs.decision_vi(bl_a));

    // (assign level, backtrack level)
    let (al, bl) = if use_chronobt {
        (
            new_learnt[1..]
                .iter()
                .map(|l| vdb[l].level)
                .max()
                .unwrap_or(0),
            cl - 1,
        )
    } else {
        (bl_a, bl_a)
    };
    let learnt_len = new_learnt.len();
    if learnt_len == 1 {
        //[PARTIAL FIXED SOLUTION by UNIT LEARNT CLAUSE GENERATION]
        // dump to certified even if it's a literal.
        cdb.certificate_add(new_learnt);
        if use_chronobt {
            asgs.cancel_until(vdb, bl);
            debug_assert!(asgs.iter().all(|l| l.vi() != l0.vi()));
            asgs.assign_by_implication(vdb, l0, ClauseId::default(), 0);
        } else {
            asgs.assign_by_unitclause(vdb, l0);
        }
        state.num_solved_vars += 1;
    } else {
        //[Reason-Side Rewarding]
        {
            // At the present time, some reason clauses can contain first UIP or its negation.
            // So we have to filter vars instead of literals to avoid double counting.
            let mut bumped = new_learnt.iter().map(|l| l.vi()).collect::<Vec<VarId>>();
            for lit in new_learnt.iter() {
                for l in &cdb[vdb[lit.vi()].reason].lits {
                    let vi = l.vi();
                    if !bumped.contains(&vi) {
                        vdb.reward_at_analysis(vi);
                        bumped.push(vi);
                    }
                }
            }
        }
        asgs.cancel_until(vdb, bl);
        let lbd = vdb.compute_lbd(&new_learnt);
        let cid = cdb.attach(state, vdb, lbd);
        elim.add_cid_occur(vdb, cid, &mut cdb[cid], true);
        state.c_lvl.update(cl as f64);
        state.b_lvl.update(bl as f64);
        asgs.assign_by_implication(vdb, l0, cid, al);
        rst.lbd.update(lbd);
        if lbd <= 2 {
            state[Stat::NumLBD2] += 1;
        }
        if learnt_len == 2 {
            state[Stat::NumBin] += 1;
            state[Stat::NumBinLearnt] += 1;
        }
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
            rst.asg.trend().min(10.0),
            rst.lbd.trend().min(10.0),
        ));
    }
    if ncnfl % state.reflection_interval == 0 {
        adapt_modules(asgs, cdb, elim, rst, state, vdb)?;
        if let Some(p) = state.elapsed() {
            if 1.0 <= p {
                return Err(SolverError::TimeOut);
            }
        } else {
            return Err(SolverError::UndescribedError);
        }
    }
    cdb.check_and_reduce(state, vdb, state[Stat::Conflict]);
    Ok(())
}

#[inline]
fn adapt_modules(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    vdb: &mut VarDB,
) -> MaybeInconsistent {
    state.check_stagnation();
    let switch = 10 * state.reflection_interval == state[Stat::Conflict];
    if switch {
        state.flush("exhaustive eliminator activated...");
        asgs.cancel_until(vdb, 0);
        state.select_strategy();
        if elim.enable {
            elim.activate();
            elim.simplify(asgs, cdb, state, vdb)?;
        }
    }
    cdb.adapt_to(state, switch);
    rst.adapt_to(state, switch);
    vdb.adapt_to(state, switch);
    state[Stat::SolvedRecord] = state.num_solved_vars;
    state.progress(cdb, rst, vdb, None);
    Ok(())
}

#[allow(clippy::cognitive_complexity)]
fn conflict_analyze(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    vdb: &mut VarDB,
    confl: ClauseId,
) -> DecisionLevel {
    let learnt = &mut state.new_learnt;
    learnt.clear();
    learnt.push(NULL_LIT);
    let dl = asgs.level();
    let mut cid = confl;
    let mut p = NULL_LIT;
    let mut ti = asgs.len() - 1; // trail index
    let mut path_cnt = 0;
    let chan_seok_condition = cdb.chan_seok_condition();
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
                    // chan_seok_condition is zero if !use_chan_seok
                    if nlevels < chan_seok_condition {
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
        while {
            let v = &vdb[asgs[ti].vi()];
            !v.is(Flag::CA_SEEN) || v.level != dl
        } {
            // println!("- skip {} because it isn't flagged", asgs[ti].int());
            debug_assert!(
                0 < ti,
                format!(
                    "lv: {}, learnt: {:?}\nconflict: {:?}",
                    dl,
                    vdb.dump(&*learnt),
                    vdb.dump(&cdb[confl].lits),
                ),
            );
            ti -= 1;
        }
        p = asgs[ti];
        let next_vi = p.vi();
        cid = vdb[next_vi].reason;
        // println!("- move to flagged {}, which reason is {}; num path: {}",
        //          next_vi, path_cnt - 1, cid.fmt());
        vdb[next_vi].turn_off(Flag::CA_SEEN);
        // since the trail can contain a literal which level is under `dl` after
        // the `dl`-th thdecision var, we must skip it.
        path_cnt -= 1;
        if path_cnt == 0 {
            break;
        }
        debug_assert!(0 < ti);
        ti -= 1;
    }
    debug_assert!(learnt.iter().all(|l| *l != !p));
    debug_assert_eq!(vdb[p].level, dl);
    learnt[0] = !p;
    // println!("- appending {}, the result is {:?}", learnt[0].int(), vec2int(learnt));
    state.simplify_learnt(asgs, cdb, vdb)
}

impl State {
    fn simplify_learnt(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        vdb: &mut VarDB,
    ) -> DecisionLevel {
        let State {
            ref mut new_learnt, ..
        } = self;
        let mut to_clear: Vec<Lit> = vec![new_learnt[0]];
        let mut levels = vec![false; asgs.level() as usize + 1];
        for l in &new_learnt[1..] {
            to_clear.push(*l);
            levels[vdb[l].level as usize] = true;
        }
        let l0 = new_learnt[0];
        new_learnt.retain(|l| *l == l0 || !l.is_redundant(cdb, vdb, &mut to_clear, &levels));
        let len = new_learnt.len();
        if 2 < len && len < 30 {
            vdb.minimize_with_biclauses(cdb, new_learnt);
        }
        // find correct backtrack level from remaining literals
        let mut level_to_return = 0;
        if 1 < new_learnt.len() {
            let mut max_i = 1;
            level_to_return = vdb[new_learnt[max_i].vi()].level;
            for (i, l) in new_learnt.iter().enumerate().skip(2) {
                let lv = vdb[l].level;
                if level_to_return < lv {
                    level_to_return = lv;
                    max_i = i;
                }
            }
            new_learnt.swap(1, max_i);
        }
        for l in &to_clear {
            vdb[l].turn_off(Flag::CA_SEEN);
        }
        level_to_return
    }
}

/// return `true` if the `lit` is redundant, which is defined by
/// any leaf of implication graph for it isn't a fixed var nor a decision var.
impl Lit {
    fn is_redundant(
        self,
        cdb: &mut ClauseDB,
        vdb: &mut VarDB,
        clear: &mut Vec<Lit>,
        levels: &[bool],
    ) -> bool {
        if vdb[self].reason == ClauseId::default() {
            return false;
        }
        let mut stack = Vec::new();
        stack.push(self);
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
                        // one of the roots is a decision var at an unchecked level.
                        for l in &clear[top..] {
                            vdb[l].turn_off(Flag::CA_SEEN);
                        }
                        clear.truncate(top);
                        return false;
                    }
                }
            }
        }
        true
    }
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
    for l in &asgs[asgs.len_upto(0)..end] {
        let vi = l.vi();
        if seen[vi] {
            if vdb[vi].reason == ClauseId::default() {
                state.conflicts.push(!*l);
            } else {
                for l in &c[(c.len() != 2) as usize..] {
                    let vj = l.vi();
                    if 0 < vdb[vj].level {
                        seen[vj] = true;
                    }
                }
            }
        }
        seen[vi] = false;
    }
}

impl VarDB {
    fn dump<'a, V: IntoIterator<Item = &'a Lit, IntoIter = Iter<'a, Lit>>>(
        &self,
        v: V,
    ) -> Vec<(i32, DecisionLevel, bool, Option<bool>)> {
        v.into_iter()
            .map(|l| {
                let v = &self[*l];
                (
                    i32::from(l),
                    v.level,
                    v.reason == ClauseId::default(),
                    v.assign,
                )
            })
            .collect::<Vec<(i32, DecisionLevel, bool, Option<bool>)>>()
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

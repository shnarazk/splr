use {
    crate::{
        clause::{Clause, ClauseDB, ClauseId},
        config::Config,
        eliminator::Eliminator,
        propagator::AssignStack,
        state::{Stat, State},
        traits::*,
        types::*,
        var::VarDB,
    },
    std::{
        fs,
        io::{BufRead, BufReader},
        path::Path,
    },
};

/// Normal results returned by Solver.
#[derive(Debug, PartialEq)]
pub enum Certificate {
    SAT(Vec<i32>),
    UNSAT,
}

/// Abnormal termination flags.
#[derive(Debug)]
pub enum SolverException {
    // StateUNSAT = 0,
    // StateSAT,
    Inconsistent,
    OutOfMemory,
    TimeOut,
    UndescribedError,
}

/// The return type of `Solver::solve`.
/// This captures the following three cases:
/// * `Certificate::SAT` -- solved with a satisfiable assignment set,
/// * `Certificate::UNSAT` -- proved that it's an unsatisfiable problem, and
/// * `SolverException::*` -- caused by a bug
pub type SolverResult = Result<Certificate, SolverException>;

/// SAT solver consisting of 5 sub modules.
#[derive(Debug)]
pub struct Solver {
    pub asgs: AssignStack, // Assignment
    pub cdb: ClauseDB,     // Clauses
    pub elim: Eliminator,  // Clause/Variable Elimination
    pub state: State,      // misc data
    pub vdb: VarDB,        // Variables
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
    /// use splr::traits::SatSolverIF;
    /// use splr::config::Config;
    /// use splr::solver::{Solver, Certificate};
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
        if !state.ok {
            return Ok(Certificate::UNSAT);
        }
        if cdb.check_size().is_err() {
            return Err(SolverException::OutOfMemory);
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
                    (_, 0) => asgs.enqueue_null(v, true),
                    (0, _) => asgs.enqueue_null(v, false),
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
                state.ok = false;
                if cdb.check_size().is_err() {
                    return Err(SolverException::OutOfMemory);
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
        vdb.initialize_reward(elim.order_enumerator());
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
                state.ok = false;
                if cdb.check_size().is_err() {
                    return Err(SolverException::OutOfMemory);
                }
                if state.is_timeout() {
                    return Err(SolverException::TimeOut);
                }
                Err(SolverException::Inconsistent)
            }
        }
    }
    /// # Examples
    ///
    /// ```
    /// use splr::traits::SatSolverIF;
    /// use splr::config::Config;
    /// use splr::solver::Solver;
    ///
    /// let config = Config::from("tests/sample.cnf");
    /// assert!(Solver::build(&config).is_ok());
    ///```
    fn build(config: &Config) -> std::io::Result<Solver> {
        let fs = fs::File::open(&config.cnf_filename)?;
        let mut rs = BufReader::new(fs);
        let mut buf = String::new();
        let mut nv: usize = 0;
        let mut nc: usize = 0;
        loop {
            buf.clear();
            match rs.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_k) => {
                    let mut iter = buf.split_whitespace();
                    if iter.next() == Some("p") && iter.next() == Some("cnf") {
                        if let Some(v) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                            if let Some(c) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                                nv = v;
                                nc = c;
                                break;
                            }
                        }
                    }
                    continue;
                }
                Err(e) => panic!("{}", e),
            }
        }
        let cnf = CNFDescription {
            num_of_variables: nv,
            num_of_clauses: nc,
            pathname: if config.cnf_filename.to_string_lossy().is_empty() {
                "--".to_string()
            } else {
                Path::new(&config.cnf_filename.to_string_lossy().into_owned())
                    .file_name()
                    .map_or("aStrangeNamed".to_string(), |f| {
                        f.to_string_lossy().into_owned()
                    })
            },
        };
        let mut s: Solver = Solver::instantiate(config, &cnf);
        loop {
            buf.clear();
            match rs.read_line(&mut buf) {
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
                        s.state.ok = false;
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(s.vdb.len() - 1, nv);
        Ok(s)
    }
    // renamed from clause_new
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId> {
        let Solver {
            ref mut asgs,
            ref mut cdb,
            ref mut elim,
            ref mut vdb,
            ..
        } = self;
        debug_assert!(asgs.level() == 0);
        if v.iter().any(|l| vdb.assigned(*l).is_some()) {
            cdb.certificate_add(v);
        }
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means tautology.
        for i in 0..v.len() {
            let li = v[i];
            let sat = vdb.assigned(li);
            if sat == Some(true) || !li == l_ {
                return Some(ClauseId::default());
            } else if sat != Some(false) && li != l_ {
                v[j] = li;
                j += 1;
                l_ = li;
            }
        }
        v.truncate(j);
        match v.len() {
            0 => None, // Empty clause is UNSAT.
            1 => {
                asgs.enqueue_null(&mut vdb[v[0].vi()], bool::from(v[0]));
                Some(ClauseId::default())
            }
            _ => {
                let cid = cdb.new_clause(&v, 0, false);
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
        vdb.update_ordinal();
        let ci = asgs.propagate(cdb, state, vdb);
        state.stats[Stat::Propagation] += 1;
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
                asgs.uncheck_assume(vdb, Lit::from_var(vi, p));
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
    let bl = analyze(asgs, cdb, state, vdb, ci);
    bump_vars(asgs, cdb, vdb, ci);
    let new_learnt = &mut state.new_learnt;
    /* for l in &new_learnt[..] {
        for lit in &cdb[vdb[l.vi()].reason].lits {
            vdb.bump_activity(lit.vi(), 0);
        }
    } */
    asgs.cancel_until(vdb, bl.max(state.root_level));
    let learnt_len = new_learnt.len();
    if learnt_len == 1 {
        // dump to certified even if it's a literal.
        cdb.certificate_add(new_learnt);
        asgs.uncheck_enqueue(vdb, new_learnt[0], ClauseId::default());
    } else {
        state.stats[Stat::Learnt] += 1;
        let lbd = vdb.compute_lbd(&new_learnt, &mut state.lbd_temp);
        let l0 = new_learnt[0];
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
        asgs.uncheck_enqueue(vdb, l0, cid);
        state.rst.lbd.update(lbd);
        state[Stat::SumLBD] += lbd;
    }
    cdb.scale_activity();
    vdb.scale_activity();
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
    if ncnfl % 10_000 == 0 {
        adapt_parameters(asgs, cdb, elim, state, vdb, ncnfl)?;
        if state.is_timeout() {
            return Err(SolverError::Inconsistent);
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
    let switch = 100_000;
    {
        let stopped = state[Stat::SolvedRecord] == state.num_solved_vars;
        if stopped {
            state.slack_duration += 1;
        } else if 0 < state.slack_duration && state.stagnated {
            state.slack_duration *= -1;
        } else {
            state.slack_duration = 0;
        }
        if stopped {
            vdb.reward_by_dl *= 0.99;
        } else {
            vdb.reward_by_dl = 1.0;
        }
        let stagnated = ((state.num_vars - state.num_solved_vars)
            .next_power_of_two()
            .trailing_zeros() as isize)
            < state.slack_duration;
        if !state.stagnated && stagnated {
            state[Stat::Stagnation] += 1;
        }
        state.stagnated = stagnated;
    }
    state[Stat::SolvedRecord] = state.num_solved_vars;
    if !state.rst.luby.active && state.rst.adaptive_restart && !state.stagnated {
        let moving: f64 = 0.04;
        let spring: f64 = 0.02;
        let margin: f64 = 0.20;
        let too_few: usize = 10;
        let too_many: usize = 1000;
        // restart_threshold
        let nr = state[Stat::Restart] - state[Stat::RestartRecord];
        state[Stat::RestartRecord] = state[Stat::Restart];
        if state.rst.lbd.threshold + moving < 1.0 && nr < too_few {
            state.rst.lbd.threshold += moving;
        } else if state.config.restart_threshold - margin <= state.rst.lbd.threshold
            && too_many < nr
        {
            state.rst.lbd.threshold -= moving;
        } else if too_few <= nr && nr <= too_many {
            state.rst.lbd.threshold -=
                (state.rst.lbd.threshold - state.config.restart_threshold) * spring;
        }

        // restart_blocking
        let _nb = state[Stat::BlockRestart] - state[Stat::BlockRestartRecord];
        state[Stat::BlockRestartRecord] = state[Stat::BlockRestart];
        /*
        if state.config.restart_blocking - margin <= state.rst.asg.threshold && nb < too_few {
            state.rst.asg.threshold -= moving;
        } else if state.rst.asg.threshold <= state.config.restart_blocking + margin && too_many < nb
        {
            state.rst.asg.threshold += moving;
        } else if too_few <= nb && nb <= too_many {
            state.rst.asg.threshold -=
                (state.rst.asg.threshold - state.config.restart_blocking) * spring;
        }
        */
    }
    if nconflict == switch {
        state.flush("exhaustive eliminator activated...");
        asgs.cancel_until(vdb, 0);
        state.adapt_strategy(cdb);
        if elim.enable {
            cdb.reset();
            elim.activate();
            cdb.simplify(asgs, elim, state, vdb)?;
        }
    }
    state.progress(cdb, vdb, None);
    if !state.config.without_deep_search {
        state.rst.restart_step = 50 + 40_000 * (state.stagnated as usize);
        if state.stagnated {
            state.flush(format!("deep searching ({})...", state.slack_duration));
            state.rst.next_restart += 80_000;
        }
    }
    Ok(())
}

fn analyze(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    vdb: &mut VarDB,
    confl: ClauseId,
) -> usize {
    let learnt = &mut state.new_learnt;
    let _cweight = asgs.conflict_weight;
    learnt.clear();
    learnt.push(NULL_LIT);
    let dl = asgs.level();
    let mut cid = confl;
    let mut p = NULL_LIT;
    let mut ti = asgs.len() - 1; // trail index
    let mut path_cnt = 0;
    state.last_dl.clear();
    loop {
        // println!("analyze {}", p.int());
        unsafe {
            debug_assert_ne!(cid, ClauseId::default());
            let c = &mut cdb[cid] as *mut Clause;
            debug_assert!(!(*c).is(Flag::DEAD));
            if (*c).is(Flag::LEARNT) {
                cdb.bump_activity(cid, ());
                if 2 < (*c).rank {
                    let nlevels = vdb.compute_lbd(&(*c).lits, &mut state.lbd_temp);
                    if nlevels + 1 < (*c).rank {
                        if (*c).rank <= cdb.lbd_frozen_clause {
                            (*c).turn_on(Flag::JUST_USED);
                        }
                        if state.use_chan_seok && nlevels < cdb.co_lbd_bound {
                            (*c).turn_off(Flag::LEARNT);
                            cdb.num_learnt -= 1;
                        } else {
                            (*c).rank = nlevels;
                        }
                    }
                }
            }
            if p != NULL_LIT && (*c).lits.len() == 2 && (*c).lits[1] == p {
                (*c).lits.swap(0, 1);
            }
            // println!("- handle {}", cid.fmt());
            for q in &(*c).lits[((p != NULL_LIT) as usize)..] {
                let vi = q.vi();
                let lvl = vdb[vi].level;
                if 0 < lvl && !state.an_seen[vi] {
                    // vdb.bump_activity(vi, ());
                    let v = &mut vdb[vi];
                    debug_assert!(!v.is(Flag::ELIMINATED));
                    debug_assert!(v.assign.is_some());
                    state.an_seen[vi] = true;
                    if dl <= lvl {
                        // println!("- flag for {} which level is {}", q.int(), lvl);
                        path_cnt += 1;
                        if v.reason != ClauseId::default() && cdb[v.reason].is(Flag::LEARNT) {
                            state.last_dl.push(*q);
                        }
                    } else {
                        // println!("- push {} to learnt, which level is {}", q.int(), lvl);
                        learnt.push(*q);
                    }
                } else {
                    // if !state.an_seen[vi] {
                    //     println!("- ignore {} because it was flagged", q.int());
                    // } else {
                    //     println!("- ignore {} because its level is {}", q.int(), lvl);
                    // }
                }
            }
            // set the index of the next literal to ti
            while !state.an_seen[asgs.trail[ti].vi()] {
                // println!("- skip {} because it isn't flagged", asgs.trail[ti].int());
                ti -= 1;
            }
            p = asgs.trail[ti];
            let next_vi = p.vi();
            cid = vdb[next_vi].reason;
            // println!("- move to flagged {}, which reason is {}; num path: {}",
            //          next_vi, path_cnt - 1, cid.fmt());
            state.an_seen[next_vi] = false;
            path_cnt -= 1;
            if path_cnt <= 0 {
                break;
            }
            ti -= 1;
        }
    }
    debug_assert_eq!(vdb[p.vi()].level, dl); // So we don't have to call bump_activity
    learnt[0] = !p;
    // println!("- appending {}, the result is {:?}", learnt[0].int(), vec2int(learnt));
    simplify_learnt(asgs, cdb, state, vdb)
}

#[allow(dead_code)]
fn bump_vars(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    vdb: &mut VarDB,
    confl: ClauseId,
) {
    let mut cid = confl;
    let mut p = NULL_LIT;
    let mut ti = asgs.len(); // trail index
    let mut seen = [false].repeat(vdb.len() + 1);
    loop {
        let c = &cdb[cid];
        if cid != ClauseId::default() {
            for q in &(*c).lits[((p != NULL_LIT) as usize)..] {
                let vi = q.vi();
                if !seen[vi] {
                    vdb.bump_activity(vi, ());
                    seen[vi] = true;
                }
            }
        }
        loop {
            if 0 == ti {
                return;
            }
            ti -= 1;
            if seen[asgs.trail[ti].vi()] {
                break;
            }
        }
        p = asgs.trail[ti];
        let next_vi = p.vi();
        cid = vdb[next_vi].reason;
        seen[next_vi] = false;
    }
}

fn simplify_learnt(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    vdb: &mut VarDB,
) -> usize {
    let State {
        ref mut new_learnt,
        ref mut an_seen,
        ..
    } = state;
    // let dl = asgs.level();
    let mut to_clear: Vec<Lit> = vec![new_learnt[0]];
    let mut levels = vec![false; asgs.level() + 1];
    for l in &new_learnt[1..] {
        to_clear.push(*l);
        levels[vdb[l.vi()].level] = true;
    }
    new_learnt.retain(|l| {
        vdb[l.vi()].reason == ClauseId::default()
            || !redundant_lit(cdb, vdb, an_seen, *l, &mut to_clear, &levels)
    });
    if new_learnt.len() < 30 {
        minimize_with_bi_clauses(cdb, vdb, &mut state.lbd_temp, new_learnt);
    }
    /*
    // glucose heuristics
    let lbd = vdb.compute_lbd(new_learnt, &mut state.lbd_temp);
    while let Some(l) = state.last_dl.pop() {
        let vi = l.vi();
        if cdb[vdb[vi].reason].rank < lbd {
            vdb.bump_activity(vi, dl);
        }
    }
    */
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
        an_seen[l.vi()] = false;
    }
    level_to_return
}

fn redundant_lit(
    cdb: &mut ClauseDB,
    vdb: &VarDB,
    seen: &mut [bool],
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
        if (*c).lits.len() == 2 && vdb.assigned((*c).lits[0]) == Some(false) {
            (*c).lits.swap(0, 1);
        }
        for q in &(*c).lits[1..] {
            let vi = q.vi();
            let lv = vdb[vi].level;
            if 0 < lv && !seen[vi] {
                if vdb[vi].reason != ClauseId::default() && levels[lv as usize] {
                    seen[vi] = true;
                    stack.push(*q);
                    clear.push(*q);
                } else {
                    for v in &clear[top..] {
                        seen[v.vi()] = false;
                    }
                    clear.truncate(top);
                    return false;
                }
            }
        }
    }
    true
}

fn analyze_final(asgs: &AssignStack, state: &mut State, vdb: &VarDB, c: &Clause) {
    let mut seen = vec![false; state.num_vars + 1];
    state.conflicts.clear();
    if asgs.level() == 0 {
        return;
    }
    for l in &c.lits {
        let vi = l.vi();
        if 0 < vdb[vi].level {
            state.an_seen[vi] = true;
        }
    }
    let end = if asgs.level() <= state.root_level {
        asgs.len()
    } else {
        asgs.num_at(state.root_level)
    };
    for l in &asgs.trail[asgs.num_at(0)..end] {
        let vi = l.vi();
        if seen[vi] {
            if vdb[vi].reason == ClauseId::default() {
                state.conflicts.push(!*l);
            } else {
                for l in &c.lits[(c.lits.len() != 2) as usize..] {
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

fn minimize_with_bi_clauses(cdb: &ClauseDB, vdb: &VarDB, temp: &mut [usize], vec: &mut Vec<Lit>) {
    let nlevels = vdb.compute_lbd(vec, temp);
    if 6 < nlevels {
        return;
    }
    let key = temp[0] + 1;
    for l in &vec[1..] {
        temp[l.vi() as usize] = key;
    }
    let l0 = vec[0];
    let mut nsat = 0;
    for w in &cdb.watcher[!l0] {
        let c = &cdb[w.c];
        if c.lits.len() != 2 {
            continue;
        }
        debug_assert!(c.lits[0] == l0 || c.lits[1] == l0);
        let other = c.lits[(c.lits[0] == l0) as usize];
        let vi = other.vi();
        if temp[vi] == key && vdb.assigned(other) == Some(true) {
            nsat += 1;
            temp[vi] -= 1;
        }
    }
    if 0 < nsat {
        temp[l0.vi()] = key;
        vec.retain(|l| temp[l.vi()] == key);
    }
    temp[0] = key;
}

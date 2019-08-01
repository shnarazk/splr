use crate::clause::{Clause, ClauseDB};
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::propagator::AssignStack;
use crate::state::{LogF64Id, Stat, State};
use crate::traits::*;
use crate::types::*;
use crate::var::VarDB;
use std::fs;
use std::io::{BufRead, BufReader};

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

impl SatSolverIF for Solver {
    fn new(config: &Config, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let elim = Eliminator::new(nv);
        let state = State::new(config, cnf.clone());
        Solver {
            asgs: AssignStack::new(nv),
            cdb: ClauseDB::new(nv, nc, config.use_certification),
            elim,
            state,
            vdb: VarDB::new(nv, config.var_activity_decay),
        }
    }
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
        if cdb.check_size(state).is_err() {
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
            for vi in 1..vdb.vars.len() {
                let v = &mut vdb.vars[vi];
                if v.assign != BOTTOM {
                    continue;
                }
                match (v.pos_occurs.len(), v.neg_occurs.len()) {
                    (_, 0) => asgs.enqueue_null(vdb, vi, TRUE),
                    (0, _) => asgs.enqueue_null(vdb, vi, FALSE),
                    (p, m) if m * 10 < p => {
                        v.phase = TRUE;
                        elim.enqueue_var(vdb, vi, false);
                    }
                    (p, m) if p * 10 < m => {
                        v.phase = FALSE;
                        elim.enqueue_var(vdb, vi, false);
                    }
                    _ => (),
                }
            }
            if !state.use_elim || !use_pre_processing_eliminator {
                elim.stop(cdb, vdb);
            }
            // state.progress(cdb, vars, Some("phase-in"));
        }
        if state.use_elim && use_pre_processing_eliminator {
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
                if cdb.check_size(state).is_err() {
                    return Err(SolverException::OutOfMemory);
                }
                return Ok(Certificate::UNSAT);
            }
            for v in &mut vdb.vars[1..] {
                if v.assign != BOTTOM || v.is(Flag::ELIMINATED) {
                    continue;
                }
                match (v.pos_occurs.len(), v.neg_occurs.len()) {
                    (_, 0) => (),
                    (0, _) => (),
                    (p, m) if m * 10 < p => v.phase = TRUE,
                    (p, m) if p * 10 < m => v.phase = FALSE,
                    _ => (),
                }
            }
        }
        state.progress(cdb, vdb, None);
        match search(asgs, cdb, elim, state, vdb) {
            Ok(true) => {
                state.progress(cdb, vdb, None);
                let mut result = Vec::new();
                for (vi, v) in vdb.vars.iter().enumerate().take(state.num_vars + 1).skip(1) {
                    match v.assign {
                        TRUE => result.push(vi as i32),
                        FALSE => result.push(0 - vi as i32),
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
                state.progress(cdb, vdb, Some("ERROR"));
                state.ok = false;
                if cdb.check_size(state).is_err() {
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
            pathname: config.cnf_filename.to_str().unwrap().to_string(),
        };
        let mut s: Solver = Solver::new(config, &cnf);
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
                            Ok(val) => v.push(Lit::from_int(val)),
                            Err(_) => (),
                        }
                    }
                    if !v.is_empty() && s.add_unchecked_clause(&mut v) == None {
                        s.state.ok = false;
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(s.vdb.vars.len() - 1, nv);
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
        if v.iter().any(|l| vdb.assigned(*l) != BOTTOM) {
            cdb.certificate_add(v);
        }
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means tautology.
        for i in 0..v.len() {
            let li = v[i];
            let sat = vdb.assigned(li);
            if sat == TRUE || li.negate() == l_ {
                return Some(NULL_CLAUSE);
            } else if sat != FALSE && li != l_ {
                v[j] = li;
                j += 1;
                l_ = li;
            }
        }
        v.truncate(j);
        match v.len() {
            0 => None, // Empty clause is UNSAT.
            1 => {
                asgs.enqueue_null(vdb, v[0].vi(), v[0].lbool());
                Some(NULL_CLAUSE)
            }
            _ => {
                let cid = cdb.new_clause(&v, 0, false);
                elim.add_cid_occur(vdb, cid, &mut cdb.clause[cid as usize], true);
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
    let mut conflict_c = 0.0; // for Luby restart
    let mut a_decision_was_made = false;
    state.restart_update_luby();
    loop {
        let ci = asgs.propagate(cdb, state, vdb);
        state.stats[Stat::Propagation] += 1;
        if ci == NULL_CLAUSE {
            if state.num_vars <= asgs.len() + state.num_eliminated_vars {
                return Ok(true);
            }
            // THE UNIFIED DYNAMIC RESTART CONTROL POINT
            if state.restart(asgs, vdb, &mut conflict_c) {
                asgs.cancel_until(vdb, state.root_level);
            } else if asgs.level() == 0 {
                if cdb.simplify(asgs, elim, state, vdb).is_err() {
                    dbg!("interal error by simplify");
                    return Err(SolverError::Inconsistent);
                }
                state.num_solved_vars = asgs.len();
            }
        /*
                    if !asgs.remains() {
                        let vi = asgs.select_var(vdb);
                        let p = vdb.vars[vi].phase;
                        asgs.uncheck_assume(vdb, Lit::from_var(vi, p));
                        state.stats[Stat::Decision] += 1;
                        a_decision_was_made = true;
                    }
        */
        } else {
            conflict_c += 1.0;
            state.stats[Stat::Conflict] += 1;
            vdb.current_conflict = state.stats[Stat::Conflict];
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state.stats[Stat::NoDecisionConflict] += 1;
            }
            if asgs.level() == state.root_level {
                analyze_final(asgs, state, vdb, &cdb.clause[ci as usize]);
                return Ok(false);
            }
            handle_conflict_path(asgs, cdb, elim, state, vdb, ci)?;
        }
        if !asgs.remains() {
            let vi = asgs.select_var(vdb);
            let p = vdb.vars[vi].phase;
            asgs.uncheck_assume(vdb, Lit::from_var(vi, p));
            state.stats[Stat::Decision] += 1;
            a_decision_was_made = true;
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
    let tn_confl = state.stats[Stat::Conflict]; // total number
    if tn_confl % 5000 == 0 && state.var_decay < state.var_decay_max {
        state.var_decay += 0.01;
    }
    state.restart_update_asg(asgs.len());
    state.c_lvl.update(asgs.level() as f64);
    let bl = analyze(asgs, cdb, state, vdb, ci);
    let new_learnt = &mut state.new_learnt;
    asgs.cancel_until(vdb, bl.max(state.root_level));
    let learnt_len = new_learnt.len();
    if learnt_len == 1 {
        // dump to certified even if it's a literal.
        cdb.certificate_add(new_learnt);
        asgs.uncheck_enqueue(vdb, new_learnt[0], NULL_CLAUSE);
        if vdb.activity_decay < 0.99 {
            vdb.activity_decay += 0.01;
        }
        state.ema_folds_ratio.update(1.0);
        state.b_lvl.update(0.0);
    } else {
        state.stats[Stat::Learnt] += 1;
        let lbd = vdb.compute_lbd(&new_learnt);
        let l0 = new_learnt[0];
        {
            let fp = vdb.bump_folding_activity(l0.vi());
            state.num_folding_vars += fp;
            state.ema_folds_ratio.update(fp as f64);
        }
        if lbd <= 2 {
            state.stats[Stat::NumLBD2] += 1;
        }
        if learnt_len == 2 {
            state.stats[Stat::NumBin] += 1;
            state.stats[Stat::NumBinLearnt] += 1;
            let l1 = new_learnt[1];
            let fp = vdb.bump_folding_activity(l1.vi());
            state.num_folding_vars += fp;
            state.ema_folds_ratio.update(fp as f64);
        }
        let cid = cdb.attach(state, vdb, lbd);
        elim.add_cid_occur(vdb, cid, &mut cdb.clause[cid as usize], true);
        state.restart_update_lbd(lbd);
        state.stats[Stat::SumLBD] += lbd;
        // Fold-based Restart Control
        let _nvar = state.num_vars - state.num_solved_vars - state.num_eliminated_vars;
        let lbd_trend = state.ema_lbd.get() * tn_confl as f64 / state.stats[Stat::SumLBD] as f64;
        let folding_ratio = state.ema_folds_ratio.get();
        let folding_trend = state.ema_folds_ratio.trend();
        let restart_ratio = state.partial_restart_ratio.get();
        let bj = (bl / 2).max(state.root_level);
        if !state.use_luby_restart
            && folding_ratio < 0.1 / (1.0 + state.stats[Stat::Restart] as f64)
            && folding_trend < 0.25
            && 1_000 < state.after_restart
        // && restart_freq < pv_ratio
        {
            // stop a exhaustive search and restart
            asgs.cancel_until(vdb, 0);
            state.b_lvl.update(0.0);
            state.partial_restart_ratio.update(1.0);
            vdb.reset_folding_points();
            vdb.activity_decay = state.config.var_activity_decay;
            state.num_folding_vars = 0;
            state.num_partial_restart = 0;
            state.num_partial_restart_try = 0;
            state.ema_folds_ratio.reinitialize1();
            state.stats[Stat::Restart] += 1;
        } else if !state.use_luby_restart
            && 1.4 < lbd_trend
            && folding_trend < 0.5
            && bj < bl
            && restart_ratio < folding_ratio
            && state.num_partial_restart_try < state.num_folding_vars
        {
            // partial restart
            asgs.cancel_until(vdb, bj);
            state.b_lvl.update(bj as f64);
            state.num_partial_restart += 1;
            state.num_partial_restart_try += 1;
            state.stats[Stat::PartialRestart] += 1;
            state.partial_restart_ratio.update(1.0); // with a bonus
        } else {
            if !state.use_luby_restart && state.num_partial_restart_try < state.num_folding_vars {
                state.num_partial_restart_try += 1;
            }
            state.b_lvl.update(bl as f64);
            asgs.uncheck_enqueue(vdb, l0, cid);
            state.partial_restart_ratio.update(0.0);
        }
    }
    if tn_confl % 10_000 == 0 {
        adapt_parameters(asgs, cdb, elim, state, vdb, tn_confl)?;
        if state.is_timeout() {
            return Err(SolverError::Inconsistent);
        }
    }
    // state.var_inc /= state.var_decay;
    state.cla_inc /= state.cla_decay;
    if ((state.use_chan_seok && !state.glureduce && state.first_reduction < cdb.num_learnt)
        || (state.glureduce
            && state.cur_restart * state.next_reduction <= state.stats[Stat::Conflict]))
        && 0 < cdb.num_learnt
    {
        state.cur_restart = ((tn_confl as f64) / (state.next_reduction as f64)) as usize + 1;
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
    if !state.use_luby_restart && switch <= nconflict {
        let stopped = state.stats[Stat::SolvedRecord] == state.num_solved_vars;
        if stopped {
            state.slack_duration += 1;
        } else {
            state.slack_duration = 0;
        }
        let stagnated = ((state.num_vars - state.num_solved_vars)
            .next_power_of_two()
            .trailing_zeros() as usize)
            < state.slack_duration;
        // && (((state.num_vars - state.num_solved_vars) as f64).log(2.0)
        //     / (state.c_lvl.get() / state.b_lvl.get()).sqrt().max(1.0)
        //     <= state.stagnation as f64)
        if !state.stagnated && stagnated {
            state.stats[Stat::Stagnation] += 1;
        }
        state.stagnated = stagnated;
    }
    state.stats[Stat::SolvedRecord] = state.num_solved_vars;
    {
        /*
        let alive = state.num_vars;
        let mut incn = 0;
        let mut fuip = 0;
        let mut minc = 0;
        let mut mfui = 0;
        let mut inou = 0;
        let mut unoi = 0;
        for v in &vars[..] {
            if 0 == v.inconsistent && 0 == v.uip {
                // done nothing
            } else if 0 < v.inconsistent {
                incn += 1;
                if 1 < v.inconsistent {
                    minc += 1;
                }
                if 0 == v.uip {
                    inou += 1;
                }
            }
            if 0 < v.uip {
                fuip += 1;
                if 1 < v.uip {
                    mfui += 1;
                }
                if 0 == v.inconsistent {
                    unoi += 1;
                }
            }
        }
        */
        /*
        state.development_history
            .push((ncnfl,
                   (state.inconsistent_sum as f64 / alive as f64),
                   (minc as f64 / alive as f64),
                   (inou as f64 / alive as f64),
                   (state.uip_sum as f64 / alive as f64),
                   (mfui as f64 / alive as f64),
                   (unoi as f64 / alive as f64),
            ));
        */
    }
    /*
        if !state.use_luby_restart && state.adaptive_restart {
            // let nr = state.stats[Stat::Restart] - state.stats[Stat::RestartRecord];
            state.stats[Stat::RestartRecord] = state.stats[Stat::Restart];
            // let nb = state.stats[Stat::BlockRestart] - state.stats[Stat::BlockRestartRecord];
            state.stats[Stat::BlockRestartRecord] = state.stats[Stat::BlockRestart];
            let margin: f64 = 0.20;
            let moving: f64 = 1.002;
            let incr = state.ema_folds_ratio.get();
            let rate = state.ema_folds_ratio.ratio();
            if state.stagnated && (1.0 < incr || 2.0 < rate) {
                if state.config.restart_threshold - margin < state.restart_thr {
                    state.restart_thr /= moving;
                }
                if state.restart_blk < state.config.restart_blocking + margin {
                    state.restart_blk *= moving;
                }
            } else if state.stagnated && (incr < 0.001 || rate < 0.5) {
                if state.restart_thr < state.config.restart_threshold + margin {
                    state.restart_thr *= moving;
                }
                if state.config.restart_blocking - margin < state.restart_blk {
                    state.restart_blk /= moving;
                }
            } else if !state.stagnated {
                // dumping restart_forcing
                if state.restart_thr < state.config.restart_threshold + margin {
                    state.restart_thr *= moving;
                } else if state.config.restart_threshold - margin < state.restart_thr {
                    state.restart_thr /= moving;
                }
                // dumping restart_blocking
                if state.restart_blk < state.config.restart_blocking + margin {
                    state.restart_blk *= moving;
                } else if state.config.restart_blocking - margin < state.restart_blk {
                    state.restart_blk /= moving;
                }
            }
        }
    */
    if nconflict == switch {
        state.flush("activating an exhaustive eliminator...");
        asgs.cancel_until(vdb, 0);
        state.adapt_strategy(cdb);
        if state.use_elim {
            // cdb.reset(state.co_lbd_bound);
            elim.activate();
            cdb.simplify(asgs, elim, state, vdb)?;
        }
    }
    // convergence stat
    if state.ema_folds_ratio.get() < state.record[LogF64Id::EmaPVInc] {
        // if vdb.activity_decay < 0.98 { vdb.activity_decay *= 1.01; }
        if 0.8 < vdb.activity_decay {
            vdb.activity_decay *= 0.98; // make sure to keep a large range
        }
        //} else {
        //    if vdb.activity_decay < 0.99 {
        //        vdb.activity_decay += 0.01;
        //    }
        //    // if 0.75 < vdb.activity_decay { vdb.activity_decay *= 0.99; }
    }
    state.progress(cdb, vdb, None);
    // if state.stagnated {
    //     state.flush(&format!("stagnated ({})...", state.slack_duration));
    // }
    if state.use_deep_search_mode {
        if state.stagnated {
            let bonus = 20_000;
            state.restart_step = 50 + bonus;
            state.next_restart += 2 * bonus;
        } else if !state.stagnated && 0 < state.stats[Stat::Stagnation] {
            state.restart_step = 1000;
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
    state.new_learnt.clear();
    state.new_learnt.push(0);
    let dl = asgs.level();
    let mut cid = confl;
    let mut p = NULL_LIT;
    let mut ti = asgs.len() - 1; // trail index
    let mut path_cnt = 0;
    state.last_dl.clear();
    loop {
        // println!("analyze {}", p.int());
        unsafe {
            debug_assert_ne!(cid, NULL_CLAUSE);
            let c = &mut cdb.clause[cid as usize] as *mut Clause;
            debug_assert!(!(*c).is(Flag::DEAD));
            if (*c).is(Flag::LEARNT) {
                cdb.bump_activity(&mut state.cla_inc, cid);
                if 2 < (*c).rank {
                    let nlevels = vdb.compute_lbd(&(*c).lits);
                    if nlevels + 1 < (*c).rank {
                        if (*c).rank <= state.lbd_frozen_clause {
                            (*c).turn_on(Flag::JUST_USED);
                        }
                        if state.use_chan_seok && nlevels < state.co_lbd_bound {
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
                let v = &mut vdb.vars[vi];
                let lvl = v.level;
                debug_assert!(!v.is(Flag::ELIMINATED));
                debug_assert!(v.assign != BOTTOM);
                if 0 < lvl && !state.an_seen[vi] {
                    state.an_seen[vi] = true;
                    if dl <= lvl {
                        // println!("- flag for {} which level is {}", q.int(), lvl);
                        path_cnt += 1;
                        if v.reason != NULL_CLAUSE && cdb.clause[v.reason as usize].is(Flag::LEARNT)
                        {
                            state.last_dl.push(*q);
                        }
                    } else {
                        // println!("- push {} to learnt, which level is {}", q.int(), lvl);
                        state.new_learnt.push(*q);
                    }
                    vdb.bump_activity(vi);
                    // Don't remove the below. This is very useful.
                    asgs.update_order(vdb, vi);
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
            cid = vdb.vars[next_vi].reason;
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
    let learnt = &mut state.new_learnt;
    learnt[0] = p.negate();
    // println!("- appending {}, the result is {:?}", learnt[0].int(), vec2int(learnt));
    simplify_learnt(asgs, cdb, state, vdb)
}

fn simplify_learnt(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    vdb: &mut VarDB,
) -> usize {
    let mut to_clear: Vec<Lit> = vec![state.new_learnt[0]];
    let mut levels = vec![false; asgs.level() + 1];
    {
        let State {
            ref mut new_learnt,
            ref mut an_seen,
            ..
        } = state;
        for l in &new_learnt[1..] {
            to_clear.push(*l);
            levels[vdb.vars[l.vi()].level] = true;
        }
        new_learnt.retain(|l| {
            vdb.vars[l.vi()].reason == NULL_CLAUSE
                || !redundant_lit(cdb, vdb, an_seen, *l, &mut to_clear, &levels)
        });
        if new_learnt.len() < 30 {
            minimize_with_bi_clauses(cdb, vdb, new_learnt);
        }
    }
    // glucose heuristics
    // let dl = asgs.level();
    // let lbd = vars.compute_lbd(&state.new_learnt, &mut state.lbd_temp);
    // while let Some(l) = state.last_dl.pop() {
    //     let vi = l.vi();
    //     if cdb.clause[vars[vi].reason as usize].rank < lbd {
    //         vars[vi].bump_activity(ncnfl);
    //         asgs.update_order(vars, vi);
    //     }
    // }
    let State {
        ref mut new_learnt, ..
    } = state;
    // find correct backtrack level from remaining literals
    let mut level_to_return = 0;
    if 1 < new_learnt.len() {
        let mut max_i = 1;
        level_to_return = vdb.vars[new_learnt[max_i].vi()].level;
        for (i, l) in new_learnt.iter().enumerate().skip(2) {
            let lv = vdb.vars[l.vi()].level;
            if level_to_return < lv {
                level_to_return = lv;
                max_i = i;
            }
        }
        new_learnt.swap(1, max_i);
    }
    for l in &to_clear {
        state.an_seen[l.vi()] = false;
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
        let cid = vdb.vars[sl.vi()].reason;
        let c = &mut cdb.clause[cid as usize];
        if (*c).lits.len() == 2 && vdb.assigned((*c).lits[0]) == FALSE {
            (*c).lits.swap(0, 1);
        }
        for q in &(*c).lits[1..] {
            let vi = q.vi();
            let lv = vdb.vars[vi].level;
            if 0 < lv && !seen[vi] {
                if vdb.vars[vi].reason != NULL_CLAUSE && levels[lv as usize] {
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
        if 0 < vdb.vars[vi].level {
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
            if vdb.vars[vi].reason == NULL_CLAUSE {
                state.conflicts.push(l.negate());
            } else {
                for l in &c.lits[(c.lits.len() != 2) as usize..] {
                    let vi = l.vi();
                    if 0 < vdb.vars[vi].level {
                        seen[vi] = true;
                    }
                }
            }
        }
        seen[vi] = false;
    }
}

fn minimize_with_bi_clauses(cdb: &ClauseDB, vdb: &mut VarDB, vec: &mut Vec<Lit>) {
    let nlevels = vdb.compute_lbd(vec);
    if 6 < nlevels {
        return;
    }
    let key = vdb.lbd_temp[0] + 1;
    for l in &vec[1..] {
        vdb.lbd_temp[l.vi() as usize] = key;
    }
    let l0 = vec[0];
    let mut nsat = 0;
    for w in &cdb.watcher[l0.negate() as usize] {
        let c = &cdb.clause[w.c as usize];
        if c.lits.len() != 2 {
            continue;
        }
        debug_assert!(c.lits[0] == l0 || c.lits[1] == l0);
        let other = c.lits[(c.lits[0] == l0) as usize];
        let vi = other.vi();
        if vdb.lbd_temp[vi] == key && vdb.assigned(other) == TRUE {
            nsat += 1;
            vdb.lbd_temp[vi] -= 1;
        }
    }
    if 0 < nsat {
        vdb.lbd_temp[l0.vi()] = key;
        vec.retain(|l| vdb.lbd_temp[l.vi()] == key);
    }
    vdb.lbd_temp[0] = key;
}

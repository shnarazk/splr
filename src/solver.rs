use crate::clause::{Clause, ClauseDB};
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::propagator::AssignStack;
use crate::state::{Stat, State};
use crate::traits::*;
use crate::types::*;
use crate::var::Var;
use std::fs;
use std::io::{BufRead, BufReader};

/// normal results returned by Solver
pub enum Certificate {
    SAT(Vec<i32>),
    UNSAT(Vec<i32>), // FIXME: replace with DRAT
}

/// abnormal termination flags
pub enum SolverException {
    StateUNSAT = 0,
    StateSAT,
    OutOfMemory,
    TimeOut,
    InternalInconsistent,
    UndescribedError,
}

/// The type that `Solver` returns
/// This captures the following three cases:
/// * solved with a satisfiable assigment,
/// * proved that it's an unsatisfiable problem, and
/// * aborted due to Mios specification or an internal error
pub type SolverResult = Result<Certificate, SolverException>;

/// is the collection of all variables.
pub struct Solver {
    pub asgs: AssignStack, // Assignment
    pub config: Config,    // Configuration
    pub cdb: ClauseDB,     // Clauses
    pub elim: Eliminator,  // Clause/Variable Elimination
    pub state: State,      // misc data
    pub vars: Vec<Var>,    // Variables
}

impl Solver {
    pub fn new(config: Config, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let elim = Eliminator::new(config.use_elim, nv);
        let state = State::new(&config, cnf.clone());
        Solver {
            asgs: AssignStack::new(nv),
            config,
            cdb: ClauseDB::new(nv, nc),
            elim,
            state,
            vars: Var::new_vars(nv),
        }
    }
}

impl SatSolverIF for Solver {
    fn solve(&mut self) -> SolverResult {
        let Solver {
            ref mut asgs,
            ref mut config,
            ref mut cdb,
            ref mut elim,
            ref mut state,
            ref mut vars,
        } = self;
        if !state.ok {
            return Ok(Certificate::UNSAT(Vec::new()));
        }
        // TODO: deal with assumptions
        // s.root_level = 0;
        state.num_solved_vars = asgs.len();
        state.progress_header(config);
        state.progress(cdb, config, elim, vars, Some("loaded"));
        if elim.in_use {
            for vi in 1..vars.len() {
                let v = &mut vars[vi];
                if v.assign != BOTTOM {
                    continue;
                }
                match (v.pos_occurs.len(), v.neg_occurs.len()) {
                    (_, 0) => {
                        asgs.enqueue_null(v, LTRUE, 0);
                    }
                    (0, _) => {
                        asgs.enqueue_null(v, LFALSE, 0);
                    }
                    _ => elim.enqueue_var(vars, vi, false),
                };
            }
            if elim.active {
                elim.activate(cdb, vars, true);
                state.progress(cdb, config, elim, vars, Some("enqueued"));
                cdb.simplify(asgs, config, elim, state, vars);
                state.progress(cdb, config, elim, vars, Some("subsumed"));
                // config.elim_eliminate_combination_limit = 40;
                // config.elim_eliminate_grow_limit = 0;
                // config.elim_eliminate_loop_limit = 32;
                // config.elim_subsume_literal_limit = 100;
                // config.elim_subsume_loop_limit = 32;
            }
            elim.stop(cdb, vars, false);
        }
        if search(asgs, config, cdb, elim, state, vars) {
            if !state.ok {
                asgs.cancel_until(vars, 0);
                state.progress(cdb, config, elim, vars, Some("error"));
                return Err(SolverException::InternalInconsistent);
            }
            state.progress(cdb, config, elim, vars, None);
            let mut result = Vec::new();
            for (vi, v) in vars.iter().enumerate().take(config.num_vars + 1).skip(1) {
                match v.assign {
                    LTRUE => result.push(vi as i32),
                    LFALSE => result.push(0 - vi as i32),
                    _ => result.push(0),
                }
            }
            elim.extend_model(&mut result);
            asgs.cancel_until(vars, 0);
            Ok(Certificate::SAT(result))
        } else {
            state.progress(cdb, config, elim, vars, None);
            asgs.cancel_until(vars, 0);
            Ok(Certificate::UNSAT(
                state.conflicts.iter().map(|l| l.int()).collect(),
            ))
        }
    }
    /// builds and returns a configured solver.
    fn build(mut config: Config, path: &str) -> (Solver, CNFDescription) {
        let mut rs = BufReader::new(fs::File::open(path).unwrap());
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
            pathname: path.to_string(),
        };
        config.num_vars = nv;
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
        debug_assert_eq!(s.vars.len() - 1, cnf.num_of_variables);
        (s, cnf)
    }
    // renamed from clause_new
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId> {
        let Solver {
            ref mut asgs,
            ref mut cdb,
            ref mut elim,
            ref mut vars,
            ..
        } = self;
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means totology.
        for i in 0..v.len() {
            let li = v[i];
            let sat = vars.assigned(li);
            if sat == LTRUE || li.negate() == l_ {
                return Some(NULL_CLAUSE);
            } else if sat != LFALSE && li != l_ {
                v[j] = li;
                j += 1;
                l_ = li;
            }
        }
        v.truncate(j);
        match v.len() {
            0 => None, // Empty clause is UNSAT.
            1 => {
                asgs.enqueue_null(&mut vars[v[0].vi()], v[0].lbool(), asgs.level());
                Some(NULL_CLAUSE)
            }
            _ => {
                let cid = cdb.new_clause(&v, 0, false);
                elim.add_cid_occur(vars, cid, &mut cdb.clause[cid], true);
                Some(cid)
            }
        }
    }
}

/// main loop; returns `true` for SAT, `false` for UNSAT.
#[inline]
fn search(
    asgs: &mut AssignStack,
    config: &mut Config,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vars: &mut [Var],
) -> bool {
    let mut conflict_c = 0.0; // for Luby restart
    let mut a_decision_was_made = false;
    state.restart_update_luby(config);
    while state.ok {
        let ci = asgs.uncheck_propagate(cdb, state, vars);
        state.stats[Stat::Propagation as usize] += 1;
        if ci == NULL_CLAUSE {
            if config.num_vars <= asgs.len() + state.num_eliminated_vars {
                return true;
            }
            // DYNAMIC FORCING RESTART
            if state.force_restart(config, &mut conflict_c) {
                asgs.cancel_until(vars, config.root_level);
            } else if asgs.level() == 0 {
                cdb.simplify(asgs, config, elim, state, vars);
                asgs.rebuild_order(&vars);
                state.num_solved_vars = asgs.len();
            }
            if !asgs.remains() {
                let vi = asgs.select_var(&vars);
                let p = vars[vi].phase;
                asgs.uncheck_assume(vars, Lit::from_var(vi, p));
                state.stats[Stat::Decision as usize] += 1;
                a_decision_was_made = true;
            }
        } else {
            conflict_c += 1.0;
            state.stats[Stat::Conflict as usize] += 1;
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state.stats[Stat::NoDecisionConflict as usize] += 1;
            }
            if asgs.level() == config.root_level {
                analyze_final(asgs, config, cdb, state, vars, ci, false);
                return false;
            }
            handle_conflict_path(asgs, config, cdb, elim, state, vars, ci);
        }
    }
    false
}

#[inline]
fn handle_conflict_path(
    asgs: &mut AssignStack,
    config: &mut Config,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vars: &mut [Var],
    ci: ClauseId,
) {
    let tn_confl = state.stats[Stat::Conflict as usize] as usize; // total number
    if tn_confl % 5000 == 0 && config.var_decay < config.var_decay_max {
        config.var_decay += 0.01;
    }
    state.restart_update_asg(config, asgs.len());
    // DYNAMIC BLOCKING RESTART
    state.block_restart(asgs, config, tn_confl);
    let mut new_learnt: Vec<Lit> = Vec::new();
    let bl = analyze(asgs, config, cdb, state, vars, ci, &mut new_learnt);
    asgs.cancel_until(vars, bl.max(config.root_level));
    let learnt_len = new_learnt.len();
    if learnt_len == 1 {
        asgs.uncheck_enqueue(vars, new_learnt[0], NULL_CLAUSE);
    } else {
        state.stats[Stat::Learnt as usize] += 1;
        let lbd = vars.compute_lbd(&new_learnt, &mut state.lbd_temp);
        let l0 = new_learnt[0];
        let cid = cdb.attach(config, elim, vars, &mut new_learnt, lbd);
        state.c_lvl.update(bl as f64);
        state.b_lvl.update(lbd as f64);
        if lbd <= 2 {
            state.stats[Stat::NumLBD2 as usize] += 1;
        }
        if learnt_len == 2 {
            state.stats[Stat::NumBin as usize] += 1;
            state.stats[Stat::NumBinLearnt as usize] += 1;
        }
        asgs.uncheck_enqueue(vars, l0, cid);
        state.restart_update_lbd(lbd);
        state.stats[Stat::SumLBD as usize] += lbd;
    }
    if tn_confl % 10_000 == 0 {
        if tn_confl == 100_000 {
            asgs.cancel_until(vars, 0);
            config.adapt_strategy(cdb, state);
        }
        // micro tuning of restart thresholds
        let nr = state.stats[Stat::Restart as usize] - state.stats[Stat::RestartRecord as usize];
        state.stats[Stat::RestartRecord as usize] = state.stats[Stat::Restart as usize];
        if config.restart_thr <= 0.82 && nr < 4 {
            config.restart_thr += 0.01;
        } else if 0.44 <= config.restart_thr && 1000 < nr {
            config.restart_thr -= 0.01;
        } else {
            config.restart_thr -= (config.restart_thr - 0.60) * 0.01
        }
        let nb = state.stats[Stat::BlockRestart as usize]
            - state.stats[Stat::BlockRestartRecord as usize];
        state.stats[Stat::BlockRestartRecord as usize] = state.stats[Stat::BlockRestart as usize];
        if 1.05 <= config.restart_blk && nb < 4 {
            config.restart_blk -= 0.01;
        } else if config.restart_blk <= 1.8 && 1000 < nb {
            config.restart_blk += 0.01;
        } else {
            config.restart_blk -= (config.restart_blk - 1.40) * 0.01
        }
        if state.stats[Stat::Elimination as usize] == 1 && state.elim_trigger == 1 {
            state.elim_trigger = state.c_lvl.get() as usize + 10;
        }
        if (state.c_lvl.get() as usize) < state.elim_trigger {
            elim.activate(cdb, vars, true);
            state.elim_trigger /= 2;
        }
        state.progress(cdb, config, elim, vars, None);
    }
    config.var_inc /= config.var_decay;
    config.cla_inc /= config.cla_decay;
    if ((config.use_chan_seok && !config.glureduce && config.first_reduction < cdb.num_learnt)
        || (config.glureduce
            && state.cur_restart * state.next_reduction <= state.stats[Stat::Conflict as usize]))
        && 0 < cdb.num_learnt
    {
        state.cur_restart = ((tn_confl as f64) / (state.next_reduction as f64)) as usize + 1;
        // if 2.0 * state.b_lvl.get() < state.c_lvl.get() {
        //     elim.activate(cdb, vars, false);
        //     let limit = state.c_lvl.get() as usize;
        //     config.elim_eliminate_combination_limit = state.ema_lbd.get() as usize;
        //     config.elim_subsume_literal_limit = limit;
        // }
        cdb.reduce(config, state, vars);
    }
}

#[inline]
fn analyze(
    asgs: &mut AssignStack,
    config: &mut Config,
    cdb: &mut ClauseDB,
    state: &mut State,
    vars: &mut [Var],
    confl: ClauseId,
    learnt: &mut Vec<Lit>,
) -> usize {
    learnt.push(0);
    let dl = asgs.level();
    let mut cid = confl;
    let mut p = NULL_LIT;
    let mut ti = asgs.len() - 1; // trail index
    let mut path_cnt = 0;
    let mut last_dl: Vec<Lit> = Vec::new();
    loop {
        // println!("analyze {}", p.int());
        unsafe {
            debug_assert_ne!(cid, NULL_CLAUSE);
            let c = &mut cdb.clause[cid] as *mut Clause;
            debug_assert!(!(*c).is(Flag::DeadClause));
            if (*c).is(Flag::LearntClause) {
                cdb.bump_activity(&mut config.cla_inc, cid);
                if 2 < (*c).rank {
                    let nlevels = vars.compute_lbd(&(*c).lits, &mut state.lbd_temp);
                    if nlevels + 1 < (*c).rank {
                        if (*c).rank <= config.lbd_frozen_clause {
                            (*c).turn_on(Flag::JustUsedClause);
                        }
                        if config.use_chan_seok && nlevels < config.co_lbd_bound {
                            (*c).turn_off(Flag::LearntClause);
                            cdb.num_learnt -= 1;
                        } else {
                            (*c).rank = nlevels;
                        }
                    }
                }
            }
            // println!("- handle {}", cid.fmt());
            for q in &(*c).lits[((p != NULL_LIT) as usize)..] {
                let vi = q.vi();
                vars.bump_activity(&mut config.var_inc, vi);
                asgs.update_order(vars, vi);
                let v = &mut vars[vi];
                let lvl = v.level;
                debug_assert!(!v.is(Flag::EliminatedVar));
                debug_assert!(v.assign != BOTTOM);
                if 0 < lvl && !state.an_seen[vi] {
                    state.an_seen[vi] = true;
                    if dl <= lvl {
                        // println!("- flag for {} which level is {}", q.int(), lvl);
                        path_cnt += 1;
                        if v.reason != NULL_CLAUSE && cdb.clause[v.reason].is(Flag::LearntClause) {
                            last_dl.push(*q);
                        }
                    } else {
                        // println!("- push {} to learnt, which level is {}", q.int(), lvl);
                        learnt.push(*q);
                    }
                } else {
                    // if !config.an_seen[vi] {
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
            cid = vars[next_vi].reason;
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
    learnt[0] = p.negate();
    // println!("- appending {}, the result is {:?}", learnt[0].int(), vec2int(learnt));
    analyze_simplify(asgs, cdb, config, state, vars, learnt, &mut last_dl)
}

// simplify phase
fn analyze_simplify(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    config: &mut Config,
    state: &mut State,
    vars: &mut [Var],
    learnt: &mut Vec<Lit>,
    last_dl: &mut Vec<Lit>,
) -> usize {
    let mut to_clear: Vec<Lit> = vec![learnt[0]];
    let mut level_map = vec![false; asgs.level() + 1];
    for l in &learnt[1..] {
        to_clear.push(*l);
        level_map[vars[l.vi()].level] = true;
    }
    learnt.retain(|l| {
        vars[l.vi()].reason == NULL_CLAUSE
            || !analyze_removable(cdb, vars, &mut state.an_seen, *l, &mut to_clear, &level_map)
    });
    if learnt.len() < 30 {
        minimize_with_bi_clauses(cdb, vars, &mut state.lbd_temp, learnt);
    }
    // glucose heuristics
    let lbd = vars.compute_lbd(learnt, &mut state.lbd_temp);
    while let Some(l) = last_dl.pop() {
        let vi = l.vi();
        if cdb.clause[vars[vi].reason].rank < lbd {
            vars.bump_activity(&mut config.var_inc, vi);
            asgs.update_order(vars, vi);
        }
    }
    // find correct backtrack level from remaining literals
    let mut level_to_return = 0;
    if 1 < learnt.len() {
        let mut max_i = 1;
        level_to_return = vars[learnt[max_i].vi()].level;
        for (i, l) in learnt.iter().enumerate().skip(2) {
            let lv = vars[l.vi()].level;
            if level_to_return < lv {
                level_to_return = lv;
                max_i = i;
            }
        }
        learnt.swap(1, max_i);
    }
    for l in &to_clear {
        state.an_seen[l.vi()] = false;
    }
    level_to_return
}

/// renamed from litRedundant
#[inline]
fn analyze_removable(
    cdb: &mut ClauseDB,
    vars: &[Var],
    an_seen: &mut [bool],
    l: Lit,
    to_clear: &mut Vec<Lit>,
    level_map: &[bool],
) -> bool {
    let mut stack = Vec::new();
    stack.push(l);
    let top = to_clear.len();
    while let Some(sl) = stack.pop() {
        let cid = vars[sl.vi()].reason;
        let c = &mut cdb.clause[cid];
        if (*c).lits.len() == 2 && vars.assigned((*c).lits[0]) == LFALSE {
            (*c).lits.swap(0, 1);
        }
        for q in &(*c).lits[1..] {
            let vi = q.vi();
            let lv = vars[vi].level;
            if 0 < lv && !an_seen[vi] {
                if vars[vi].reason != NULL_CLAUSE && level_map[lv as usize] {
                    an_seen[vi] = true;
                    stack.push(*q);
                    to_clear.push(*q);
                } else {
                    for v in &to_clear[top..] {
                        an_seen[v.vi()] = false;
                    }
                    to_clear.truncate(top);
                    return false;
                }
            }
        }
    }
    true
}

#[inline]
fn analyze_final(
    asgs: &AssignStack,
    config: &mut Config,
    cdb: &ClauseDB,
    state: &mut State,
    vars: &[Var],
    ci: ClauseId,
    skip_first: bool,
) {
    let mut seen = vec![false; config.num_vars + 1];
    state.conflicts.clear();
    if config.root_level != 0 {
        let c = &cdb.clause[ci];
        for l in &c.lits[skip_first as usize..] {
            let vi = l.vi();
            if 0 < vars[vi].level {
                state.an_seen[vi] = true;
            }
        }
        let tl0 = asgs.num_at(0);
        let start = if asgs.level() <= config.root_level {
            asgs.len()
        } else {
            asgs.num_at(config.root_level)
        };
        for l in &asgs.trail[tl0..start] {
            let vi = l.vi();
            if seen[vi] {
                if vars[vi].reason == NULL_CLAUSE {
                    state.conflicts.push(l.negate());
                } else {
                    for l in &c.lits[1..] {
                        let vi = l.vi();
                        if 0 < vars[vi].level {
                            seen[vi] = true;
                        }
                    }
                }
            }
            seen[vi] = false;
        }
    }
}

#[inline]
fn minimize_with_bi_clauses(
    cdb: &ClauseDB,
    vars: &[Var],
    lbd_temp: &mut [usize],
    vec: &mut Vec<Lit>,
) {
    let nlevels = vars.compute_lbd(vec, lbd_temp);
    if 6 < nlevels {
        return;
    }
    let key = lbd_temp[0] + 1;
    for l in &vec[1..] {
        lbd_temp[l.vi() as usize] = key;
    }
    let l0 = vec[0];
    let mut nsat = 0;
    for w in &cdb.watcher[l0.negate() as usize][1..] {
        let c = &cdb.clause[w.c];
        if c.lits.len() != 2 {
            continue;
        }
        debug_assert!(c.lits[0] == l0 || c.lits[1] == l0);
        let other = c.lits[(c.lits[0] == l0) as usize];
        let vi = other.vi();
        if lbd_temp[vi] == key && vars.assigned(other) == LTRUE {
            nsat += 1;
            lbd_temp[vi] -= 1;
        }
    }
    if 0 < nsat {
        lbd_temp[l0.vi()] = key;
        vec.retain(|l| lbd_temp[l.vi()] == key);
    }
    lbd_temp[0] = key;
}

use crate::assign::AssignStack;
use crate::clause::{Clause, ClauseDB, ClauseFlag, ClauseKind, Watch};
use crate::config::SolverConfig;
use crate::eliminator::Eliminator;
use crate::state::{SolverState, Stat};
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
    /// major sub modules
    pub asgs: AssignStack,    // Assignment
    pub config: SolverConfig, // Configuration
    pub cps: ClauseDB,        // Clauses
    pub elim: Eliminator,     // Clause/Variable Elimination
    pub state: SolverState,   // misc data
    pub vars: Vec<Var>,       // Variables
}

impl Solver {
    pub fn new(config: SolverConfig, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let path = &cnf.pathname;
        let (_fe, se) = config.ema_coeffs;
        let mut elim = Eliminator::default();
        elim.in_use = config.use_sve && nc < 800_000 && 1000 < nv;
        let state = SolverState::new(&config, nv, se, &path.to_string());
        Solver {
            asgs: AssignStack::new(nv),
            config,
            cps: ClauseDB::new(nv, nc),
            elim,
            state,
            vars: Var::new_vars(nv),
        }
    }
}

impl SatSolver for Solver {
    fn solve(&mut self) -> SolverResult {
        let Solver {
            ref mut asgs,
            ref mut config,
            ref mut cps,
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
        state.progress(config, cps, elim, vars, Some(""));
        if elim.in_use {
            for v in &mut vars[1..] {
                debug_assert!(!v.eliminated);
                debug_assert!(!asgs.trail.contains(&v.index.lit(LTRUE)));
                debug_assert!(!asgs.trail.contains(&v.index.lit(LFALSE)));
                if v.neg_occurs.is_empty() && !v.pos_occurs.is_empty() && v.assign == BOTTOM {
                    asgs.enqueue_null(v, LTRUE, 0);
                } else if v.pos_occurs.is_empty() && !v.neg_occurs.is_empty() && v.assign == BOTTOM
                {
                    asgs.enqueue_null(v, LFALSE, 0);
                } else if v.pos_occurs.len() == 1 || v.neg_occurs.len() == 1 {
                    elim.enqueue_var(v);
                }
            }
            if elim.active {
                cps.simplify(asgs, config, elim, state, vars);
                state.progress(config, cps, elim, vars, Some("simplify"));
            } else {
                elim.stop(cps,vars, false);
                state.progress(config, cps, elim, vars, Some("loaded"));
            }
        } else {
            state.progress(config, cps, elim, vars, Some("loaded"));
        }
        if search(asgs, config, cps, elim, state, vars) {
            if !state.ok {
                asgs.cancel_until(vars, &mut state.var_order, 0);
                state.progress(config, cps, elim, vars, Some("error"));
                return Err(SolverException::InternalInconsistent);
            }
            state.progress(config, cps, elim, vars, None);
            let mut result = Vec::new();
            for (vi, v) in vars.iter().enumerate().take(config.num_vars + 1).skip(1) {
                match v.assign {
                    LTRUE => result.push(vi as i32),
                    LFALSE => result.push(0 - vi as i32),
                    _ => result.push(0),
                }
            }
            elim.extend_model(&mut result);
            asgs.cancel_until(vars, &mut state.var_order, 0);
            Ok(Certificate::SAT(result))
        } else {
            state.progress(config, cps, elim, vars, None);
            asgs.cancel_until(vars, &mut state.var_order, 0);
            Ok(Certificate::UNSAT(
                state.conflicts.iter().map(|l| l.int()).collect(),
            ))
        }
    }

    /// builds and returns a configured solver.
    fn build(mut cfg: SolverConfig, path: &str) -> (Solver, CNFDescription) {
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
        //let mut cfg = SolverConfig::default();
        cfg.num_vars = nv;
        let mut s: Solver = Solver::new(cfg, &cnf);
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
                            Ok(val) => v.push(int2lit(val)),
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
            ref mut cps,
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
        let kind = if v.len() == 2 {
            ClauseKind::Binclause
        } else {
            ClauseKind::Permanent
        };
        match v.len() {
            0 => None, // Empty clause is UNSAT.
            1 => {
                asgs.enqueue_null(&mut vars[v[0].vi()], v[0].lbool(), asgs.level());
                Some(NULL_CLAUSE)
            }
            _ => {
                let cid = cps[kind as usize].new_clause(&v, 0);
                vars.attach_clause(elim, cid, clause_mut!(*cps, cid), true);
                Some(cid)
            }
        }
    }
}

impl Propagate for AssignStack {
    fn propagate(
        &mut self,
        cps: &mut ClauseDB,
        state: &mut SolverState,
        vars: &mut [Var],
    ) -> ClauseId {
        while self.remains() {
            let p: usize = self.sweep() as usize;
            let false_lit = (p as Lit).negate();
            state.stats[Stat::Propagation as usize] += 1;
            for kind in &[
                ClauseKind::Binclause,
                ClauseKind::Removable,
                ClauseKind::Permanent,
            ] {
                let head = &mut cps[*kind as usize].head;
                unsafe {
                    let watcher = &mut cps[*kind as usize].watcher[..] as *mut [Vec<Watch>];
                    let source = &mut (*watcher)[p];
                    let mut n = 1;
                    'next_clause: while n <= source.count() {
                        let w = &mut source[n];
                        if head[w.c].get_flag(ClauseFlag::Dead) {
                            source.detach(n);
                            continue 'next_clause;
                        }
                        if vars.assigned(w.blocker) != LTRUE {
                            let Clause { ref mut lits, .. } = &mut head[w.c];
                            debug_assert!(2 <= lits.len());
                            debug_assert!(lits[0] == false_lit || lits[1] == false_lit);
                            let mut first = *lits.get_unchecked(0);
                            if first == false_lit {
                                lits.swap(0, 1); // now false_lit is lits[1].
                                first = *lits.get_unchecked(0);
                            }
                            let first_value = vars.assigned(first);
                            // If 0th watch is true, then clause is already satisfied.
                            if first != w.blocker && first_value == LTRUE {
                                w.blocker = first;
                                n += 1;
                                continue 'next_clause;
                            }
                            for (k, lk) in lits.iter().enumerate().skip(2) {
                                // below is equivalent to 'assigned(lk) != LFALSE'
                                if (((lk & 1) as u8) ^ vars[lk.vi()].assign) != 0 {
                                    (*watcher)[lk.negate() as usize].attach(first, w.c);
                                    source.detach(n);
                                    lits[1] = *lk;
                                    lits[k] = false_lit;
                                    continue 'next_clause;
                                }
                            }
                        let cid = ClauseId::from_(*kind, w.c);
                            if first_value == LFALSE {
                                self.catchup();
                                return cid;
                            } else {
                                self.uncheck_enqueue(vars, first, cid);
                            }
                        }
                        n += 1;
                    }
                }
            }
        }
        NULL_CLAUSE
    }
}

#[inline(always)]
fn propagate_fast(
    asgs: &mut AssignStack,
    cps: &mut ClauseDB,
    state: &mut SolverState,
    vars: &mut [Var],
) -> ClauseId {
    while asgs.remains() {
        let p: usize = asgs.sweep() as usize;
        let false_lit = (p as Lit).negate();
        state.stats[Stat::Propagation as usize] += 1;
        for kind in &[
            ClauseKind::Binclause,
            ClauseKind::Removable,
            ClauseKind::Permanent,
        ] {
            let head = &mut cps[*kind as usize].head;
            unsafe {
                let watcher = &mut cps[*kind as usize].watcher[..] as *mut [Vec<Watch>];
                let source = &mut (*watcher)[p];
                let mut n = 1;
                'next_clause: while n <= source.count() {
                    let w = source.get_unchecked_mut(n);
                    // if head[w.c].get_flag(ClauseFlag::Dead) {
                    //     source.detach(n);
                    //     continue 'next_clause;
                    // }
                    // debug_assert!(!vars[w.blocker.vi()].eliminated); it doesn't hold in TP12
                    if vars.assigned(w.blocker) != LTRUE {
                        let Clause { ref mut lits, .. } = head.get_unchecked_mut(w.c);
                        debug_assert!(2 <= lits.len());
                        debug_assert!(lits[0] == false_lit || lits[1] == false_lit);
                        let mut first = *lits.get_unchecked(0);
                        if first == false_lit {
                            lits.swap(0, 1); // now false_lit is lits[1].
                            first = *lits.get_unchecked(0);
                        }
                        let first_value = vars.assigned(first);
                        // If 0th watch is true, then clause is already satisfied.
                        if first != w.blocker && first_value == LTRUE {
                            w.blocker = first;
                            n += 1;
                            continue 'next_clause;
                        }
                        for (k, lk) in lits.iter().enumerate().skip(2) {
                            // below is equivalent to 'assigned(lk) != LFALSE'
                            if (((lk & 1) as u8) ^ vars.get_unchecked(lk.vi()).assign) != 0 {
                                (*watcher)[lk.negate() as usize].attach(first, w.c);
                                source.detach(n);
                                lits[1] = *lk;
                                lits[k] = false_lit;
                                continue 'next_clause;
                            }
                        }
                        let cid = ClauseId::from_(*kind, w.c);
                        if first_value == LFALSE {
                            asgs.catchup();
                            return cid;
                        } else {
                            asgs.uncheck_enqueue(vars, first, cid);
                        }
                    }
                    n += 1;
                }
            }
        }
    }
    NULL_CLAUSE
}

/// main loop; returns `true` for SAT, `false` for UNSAT.
#[inline(always)]
fn search(
    asgs: &mut AssignStack,
    config: &mut SolverConfig,
    cps: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut SolverState,
    vars: &mut [Var],
) -> bool {
    let mut conflict_c = 0.0; // for Luby restart
    let mut a_decision_was_made = false;
    state.restart_update_luby(config);
    loop {
        let ci = propagate_fast(asgs, cps, state, vars);
        state.stats[Stat::Propagation as usize] += 1;
        if ci == NULL_CLAUSE {
            if config.num_vars <= asgs.len() + state.num_eliminated_vars {
                return true;
            }
            // DYNAMIC FORCING RESTART
            if state.force_restart(config, &mut conflict_c) {
                asgs.cancel_until(vars, &mut state.var_order, config.root_level);
            } else if asgs.level() == 0 {
                cps.simplify(asgs, config, elim, state, vars);
                state.var_order.rebuild(&vars);
            }
            if asgs.level() == 0 {
                if !state.ok {
                    return false;
                }
                state.num_solved_vars = asgs.len();
            }
            if !asgs.remains() {
                let vi = state.var_order.select_var(&vars);
                let p = vars[vi].phase;
                asgs.uncheck_assume(vars, elim, vi.lit(p));
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
                analyze_final(asgs, config, cps, state, vars, ci, false);
                return false;
            }
            handle_conflict_path(asgs, config, cps, elim, state, vars, ci);
            if !state.ok {
                return false;
            }
        }
    }
}

#[inline]
fn handle_conflict_path(
    asgs: &mut AssignStack,
    config: &mut SolverConfig,
    cps: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut SolverState,
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
    let bl = analyze(asgs, config, cps, state, vars, ci, &mut new_learnt);
    asgs.cancel_until(vars, &mut state.var_order, bl.max(config.root_level));
    let learnt_len = new_learnt.len();
    if learnt_len == 1 {
        asgs.uncheck_enqueue(vars, new_learnt[0], NULL_CLAUSE);
    } else {
        state.stats[Stat::Learnt as usize] += 1;
        let lbd = vars.compute_lbd(&new_learnt, &mut state.lbd_temp);
        let l0 = new_learnt[0];
        let cid = cps.add_clause(config, elim, vars, &mut new_learnt, lbd);
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
        state.stats[Stat::SumLBD as usize] += lbd as i64;
    }
    if tn_confl % 10_000 == 0 {
        state.progress(config, cps, elim, vars, None);
    }
    if tn_confl == 100_000 {
        asgs.cancel_until(vars, &mut state.var_order, 0);
        config.adapt_strategy(cps, elim, state, vars);
    }
    // decay activities
    config.var_inc /= config.var_decay;
    config.cla_inc /= config.cla_decay;
    // glucose reduction
    if (config.use_chan_seok
        && !config.glureduce
        && config.first_reduction < cps[ClauseKind::Removable as usize].count(true))
        || (config.glureduce
            && state.cur_restart * state.next_reduction
                <= (state.stats[Stat::Learnt as usize] - state.stats[Stat::NumBinLearnt as usize])
                    as usize)
    {
        state.cur_restart = ((tn_confl as f64) / (state.next_reduction as f64)) as usize + 1;
        cps.reduce(elim, state, vars);
        state.next_reduction += config.inc_reduce_db;
    }
}

#[inline(always)]
fn analyze(
    asgs: &mut AssignStack,
    config: &mut SolverConfig,
    cps: &mut ClauseDB,
    state: &mut SolverState,
    vars: &mut [Var],
    confl: ClauseId,
    learnt: &mut Vec<Lit>,
) -> usize {
    learnt.push(0);
    let dl = asgs.level();
    let mut cid: usize = confl;
    let mut p = NULL_LIT;
    let mut ti = asgs.len() - 1; // trail index
    let mut path_cnt = 0;
    loop {
        // println!("analyze {}", p.int());
        unsafe {
            let ch = clause_mut!(*cps, cid) as *mut Clause;
            debug_assert_ne!(cid, NULL_CLAUSE);
            if cid.to_kind() == ClauseKind::Removable as usize {
                // self.bump_cid(cid);
                cps[ClauseKind::Removable as usize].bump_activity(
                    &mut config.cla_inc,
                    cid.to_index(),
                    state.stats[Stat::Conflict as usize] as f64,
                );
                // if 2 < (*ch).rank {
                //     let nblevels = compute_lbd(vars, &ch.lits, lbd_temp);
                //     if nblevels + 1 < (*ch).rank {
                //         (*ch).rank = nblevels;
                //         if nblevels <= 30 {
                //             (*ch).flag_on(ClauseFlag::JustUsed);
                //         }
                //         if self.strategy == Some(SearchStrategy::ChanSeok)
                //             && nblevels < self.co_lbd_bound
                //         {
                //             (*ch).rank = 0;
                //             clause_mut!(*cps, confl).rank = 0
                //         }
                //     }
                // }
            }
            // println!("- handle {}", cid.fmt());
            for q in &(*ch).lits[((p != NULL_LIT) as usize)..] {
                let vi = q.vi();
                let lvl = vars[vi].level;
                debug_assert!(!(*ch).get_flag(ClauseFlag::Dead));
                debug_assert!(
                    !vars[vi].eliminated,
                    format!("analyze assertion: an eliminated var {} occurs", vi)
                );
                // debug_assert!(
                //     vars[vi].assign != BOTTOM,
                //     format!("{:?} was assigned", vars[vi])
                // );
                vars.bump_activity(
                    &mut config.var_inc,
                    vi,
                    state.stats[Stat::Conflict as usize] as f64,
                );
                state.var_order.update(vars, vi);
                if 0 < lvl && !state.an_seen[vi] {
                    state.an_seen[vi] = true;
                    if dl <= lvl {
                        // println!("- flag for {} which level is {}", q.int(), lvl);
                        path_cnt += 1;
                    // if vars[vi].reason != NULL_CLAUSE
                    //     && vars[vi].reason.to_kind() == ClauseKind::Removable as usize
                    // {
                    //     last_dl.push(*q);
                    // }
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
    debug_assert_eq!(learnt[0], 0);
    learnt[0] = p.negate();
    debug_assert_ne!(learnt[0], 0);
    // println!("- append {}; the result is {:?}", p.negate().int(), vec2int(learnt));
    // simplify phase
    let mut to_clear = Vec::new();
    to_clear.push(p.negate());
    let mut level_map = vec![false; asgs.level() + 1];
    for l in &learnt[1..] {
        to_clear.push(*l);
        level_map[vars[l.vi()].level] = true;
    }
    learnt.retain(|l| {
        vars[l.vi()].reason == NULL_CLAUSE
            || !analyze_removable(cps, vars, &mut state.an_seen, *l, &mut to_clear, &level_map)
    });
    if learnt.len() < 30 {
        minimize_with_bi_clauses(cps, vars, &mut state.lbd_temp, learnt);
    }
    // glucose heuristics
    // let lbd = vars.compute_lbd(learnt, lbd_temp);
    // while let Some(l) = last_dl.pop() {
    //     let vi = l.vi();
    //     if clause!(*cps, vars[vi].reason).rank < lbd {
    //         vars.bump_activity(vi, &mut config.var_inc, state.stats[Stat::Conflict as usize] as f64);
    //         var_order.update(vars, vi);
    //     }
    // }
    // find correct backtrack level from remaining literals
    let mut level_to_return = 0;
    if 1 < learnt.len() {
        let mut max_i = 1;
        level_to_return = vars[learnt[max_i].vi()].level;
        // for i in 2..learnt.len() {
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
#[inline(always)]
fn analyze_removable(
    cps: &mut ClauseDB,
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
        let ch = clause_mut!(*cps, cid);
        if (*ch).lits.len() == 2 && vars.assigned((*ch).lits[0]) == LFALSE {
            (*ch).lits.swap(0, 1);
        }
        for q in &(*ch).lits[1..] {
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

#[inline(always)]
fn analyze_final(
    asgs: &AssignStack,
    config: &mut SolverConfig,
    cps: &ClauseDB,
    state: &mut SolverState,
    vars: &[Var],
    ci: ClauseId,
    skip_first: bool,
) {
    let mut seen = vec![false; config.num_vars + 1];
    state.conflicts.clear();
    if config.root_level != 0 {
        let ch = clause!(*cps, ci);
        for l in &ch.lits[skip_first as usize..] {
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
                    for l in &ch.lits[1..] {
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

#[inline(always)]
fn minimize_with_bi_clauses(
    cps: &ClauseDB,
    vars: &[Var],
    lbd_temp: &mut [usize],
    vec: &mut Vec<Lit>,
) {
    let nblevels = vars.compute_lbd(vec, lbd_temp);
    if 6 < nblevels {
        return;
    }
    // reuse lbd_temp scretely
    let key = lbd_temp[0] + 1;
    for l in &vec[1..] {
        lbd_temp[l.vi() as usize] = key;
    }
    let l0 = vec[0];
    let mut nb = 0;
    let len = cps[ClauseKind::Binclause as usize].watcher[l0.negate() as usize].count();
    if len == 0 {
        lbd_temp[0] = key;
        return;
    }
    for w in &cps[ClauseKind::Binclause as usize].watcher[l0.negate() as usize][1..len] {
        let ch = &cps[ClauseKind::Binclause as usize].head[w.c];
        debug_assert!(ch.lits[0] == l0 || ch.lits[1] == l0);
        let other = ch.lits[(ch.lits[0] == l0) as usize];
        let vi = other.vi();
        if lbd_temp[vi] == key && vars.assigned(other) == LTRUE {
            nb += 1;
            lbd_temp[vi] -= 1;
        }
    }
    if 0 < nb {
        lbd_temp[l0.vi()] = key;
        vec.retain(|l| lbd_temp[l.vi()] == key);
    }
    lbd_temp[0] = key;
}

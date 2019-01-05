use crate::assign::AssignStack;
use crate::clause::{ClauseManagement, GC, *};
use crate::eliminator::{Eliminator, EliminatorIF};
use crate::restart::{luby, QueueOperations, RESTART_BLK, RESTART_THR};
use crate::state::*;
use crate::types::*;
use crate::var::{VarOrdering, *};
use std::cmp::max;
use std::fs;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};

/// For Solver
pub trait SatSolver {
    fn solve(&mut self) -> SolverResult;
    fn build(path: &str) -> (Solver, CNFDescription);
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

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

#[derive(Eq, PartialEq)]
pub enum SearchStrategy {
    Initial,
    Generic,
    LowDecisions,
    HighSuccesive,
    LowSuccesive,
    ManyGlues,
}

impl SearchStrategy {
    fn to_str(&self) -> &'static str {
        match self {
            SearchStrategy::Initial => "init",
            SearchStrategy::Generic => "dflt",
            SearchStrategy::LowDecisions => "LowD",
            SearchStrategy::HighSuccesive => "High",
            SearchStrategy::LowSuccesive => "LowS",
            SearchStrategy::ManyGlues => "Many",
        }
    }
}

/// `Solver`'s parameters; random decision rate was dropped.
pub struct SolverConfiguration {
    pub root_level: usize,
    pub num_vars: usize,
    /// STARATEGY
    pub adapt_strategy: bool,
    pub strategy: SearchStrategy,
    pub use_chan_seok: bool,
    pub co_lbd_bound: usize,
    /// CLAUSE/VARIABLE ACTIVITY
    pub cla_decay: f64,
    pub cla_inc: f64,
    pub var_decay: f64,
    pub var_decay_max: f64,
    pub var_inc: f64,
    /// CLAUSE REDUCTION
    pub first_reduction: usize,
    pub glureduce: bool,
    pub inc_reduce_db: usize,
    pub inc_reduce_db_extra: usize,
    pub ema_coeffs: (i32, i32),
    /// RESTART
    pub restart_thr: f64,
    pub restart_blk: f64,
    pub restart_expansion: f64,
    pub restart_step: f64,
    pub luby_restart: bool,
    pub luby_restart_num_conflict: f64,
    pub luby_restart_inc: f64,
    pub luby_current_restarts: usize,
    pub luby_restart_factor: f64,
    /// MISC
    pub use_sve: bool,
    pub use_tty: bool,
    /// dump stats data during solving
    pub dump_solver_stat_mode: i32,
}

impl Default for SolverConfiguration {
    fn default() -> SolverConfiguration {
        SolverConfiguration {
            root_level: 0,
            num_vars: 0,
            adapt_strategy: true,
            strategy: SearchStrategy::Initial,
            use_chan_seok: false,
            co_lbd_bound: 5,
            cla_decay: 0.999,
            cla_inc: 1.0,
            var_decay: 0.9,
            var_decay_max: 0.95,
            var_inc: 0.9,
            first_reduction: 1000,
            glureduce: false,
            inc_reduce_db: 300,
            inc_reduce_db_extra: 1000,
            restart_thr: RESTART_THR,
            restart_blk: RESTART_BLK,
            restart_expansion: 1.15,
            restart_step: 100.0,
            luby_restart: false,
            luby_restart_num_conflict: 0.0,
            luby_restart_inc: 2.0,
            luby_current_restarts: 0,
            luby_restart_factor: 100.0,
            ema_coeffs: (2 ^ 5, 2 ^ 15),
            use_sve: true,
            use_tty: true,
            dump_solver_stat_mode: 0,
        }
    }
}

/// is the collection of all variables.
pub struct Solver {
    /// major sub modules
    pub asgs: AssignStack,
    pub config: SolverConfiguration, // Configuration
    pub cps: ClauseDB,               // Clauses
    pub elim: Eliminator,            // Clause/Variable Elimination
    pub state: SolverState,
    pub vars: Vec<Var>, // Variables
}

const LBD_QUEUE_LEN: usize = 50;
const TRAIL_QUEUE_LEN: usize = 5000;

impl Solver {
    pub fn new(config: SolverConfiguration, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let path = &cnf.pathname;
        let (_fe, se) = config.ema_coeffs;
        let sve = config.use_sve;
        Solver {
            asgs: AssignStack::new(nv),
            config,
            cps: [
                ClausePartition::build(ClauseKind::Liftedlit, nv, 0),
                ClausePartition::build(ClauseKind::Removable, nv, nc),
                ClausePartition::build(ClauseKind::Permanent, nv, 256),
                ClausePartition::build(ClauseKind::Binclause, nv, 256),
            ],
            elim: Eliminator::new(sve),
            state: SolverState::new(nv, se, &path.to_string()),
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
        progress(asgs, config, cps, elim, state, vars, Some(""));
        // elim.use_elim = true;
        elim.var_queue.clear();
        if elim.use_elim {
            for v in &mut vars[1..] {
                if v.neg_occurs.is_empty() && !v.pos_occurs.is_empty() && v.assign == BOTTOM {
                    debug_assert!(!v.eliminated);
                    debug_assert!(!asgs.trail.contains(&v.index.lit(LTRUE)));
                    debug_assert!(!asgs.trail.contains(&v.index.lit(LFALSE)));
                    v.assign = LTRUE;
                    asgs.push(v.index.lit(LTRUE));
                } else if v.pos_occurs.is_empty() && !v.neg_occurs.is_empty() && v.assign == BOTTOM
                {
                    debug_assert!(!v.eliminated);
                    debug_assert!(!asgs.trail.contains(&v.index.lit(LTRUE)));
                    debug_assert!(!asgs.trail.contains(&v.index.lit(LFALSE)));
                    v.assign = LFALSE;
                    asgs.push(v.index.lit(LFALSE));
                } else if v.pos_occurs.len() == 1 || v.neg_occurs.len() == 1 {
                    elim.enqueue_var(v);
                }
            }
            progress(asgs, config, cps, elim, state, vars, Some("load"));
            cps.simplify(asgs, config, elim, state, vars);
            progress(asgs, config, cps, elim, state, vars, Some("simp"));
        } else {
            progress(asgs, config, cps, elim, state, vars, Some("load"));
        }
        // config.use_sve = false;
        // elim.use_elim = false;
        state.stat[Stat::Simplification as usize] += 1;
        if search(asgs, config, cps, elim, state, vars) {
            if !state.ok {
                asgs.cancel_until(vars, &mut state.var_order, 0);
                progress(asgs, config, cps, elim, state, vars, Some("error"));
                return Err(SolverException::InternalInconsistent);
            }
            progress(asgs, config, cps, elim, state, vars, None);
            let mut result = Vec::new();
            for (vi, v) in vars.iter().enumerate().take(config.num_vars + 1).skip(1) {
                match v.assign {
                    LTRUE => result.push(vi as i32),
                    LFALSE => result.push(0 - vi as i32),
                    _ => result.push(0),
                }
            }
            if elim.use_elim {
                elim.extend_model(&mut result);
            }
            asgs.cancel_until(vars, &mut state.var_order, 0);
            Ok(Certificate::SAT(result))
        } else {
            progress(asgs, config, cps, elim, state, vars, None);
            asgs.cancel_until(vars, &mut state.var_order, 0);
            Ok(Certificate::UNSAT(
                state.conflicts.iter().map(|l| l.int()).collect(),
            ))
        }
    }

    /// builds and returns a configured solver.
    fn build(path: &str) -> (Solver, CNFDescription) {
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
        let mut cfg = SolverConfiguration::default();
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
                vars.attach_clause(cid, clause_mut!(*cps, cid), true, elim);
                Some(cid)
            }
        }
    }
}

pub fn propagate(
    asgs: &mut AssignStack,
    cp: &mut ClauseDB,
    state: &mut SolverState,
    vars: &mut [Var],
) -> ClauseId {
    while asgs.remains() {
        let p: usize = asgs.sweep() as usize;
        let false_lit = (p as Lit).negate();
        state.stat[Stat::Propagation as usize] += 1;
        for kind in &[
            ClauseKind::Binclause,
            ClauseKind::Removable,
            ClauseKind::Permanent,
        ] {
            let head = &mut cp[*kind as usize].head[..];
            unsafe {
                let watcher = &mut cp[*kind as usize].watcher[..] as *mut [Vec<Watch>];
                let source = &mut (*watcher)[p];
                let mut n = 1;
                'next_clause: while n <= source.count() {
                    let w = &mut source[n];
                    if (*head)[w.c].get_flag(ClauseFlag::Dead) {
                        source.detach(n);
                        continue 'next_clause;
                    }
                    if vars.assigned(w.blocker) != LTRUE {
                        let ClauseHead { ref mut lits, .. } = &mut (*head)[w.c];
                        debug_assert!(2 <= lits.len());
                        debug_assert!(lits[0] == false_lit || lits[1] == false_lit);
                        if lits[0] == false_lit {
                            lits.swap(0, 1); // now false_lit is lits[1].
                        }
                        let first = lits[0];
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
                        if first_value == LFALSE {
                            asgs.catchup();
                            // println!("conflict by {} {:?}", cid2fmt(kind.id_from(w.c)), vec2int(&lits));
                            return kind.id_from(w.c);
                        } else {
                            asgs.uncheck_enqueue(vars, first, kind.id_from(w.c));
                        }
                    }
                    n += 1;
                }
            }
        }
    }
    NULL_CLAUSE
}

#[inline(always)]
fn propagate_fast(
    asgs: &mut AssignStack,
    cp: &mut ClauseDB,
    state: &mut SolverState,
    vars: &mut [Var],
) -> ClauseId {
    while asgs.remains() {
        let p: usize = asgs.sweep() as usize;
        let false_lit = (p as Lit).negate();
        state.stat[Stat::Propagation as usize] += 1;
        for kind in &[
            ClauseKind::Binclause,
            ClauseKind::Removable,
            ClauseKind::Permanent,
        ] {
            let head = &mut cp[*kind as usize].head[..];
            unsafe {
                let watcher = &mut cp[*kind as usize].watcher[..] as *mut [Vec<Watch>];
                let source = &mut (*watcher)[p];
                let mut n = 1;
                'next_clause: while n <= source.count() {
                    let w = &mut source[n];
                    // if (*head)[w.c].get_flag(ClauseFlag::Dead) {
                    //     source.detach(n);
                    //     continue 'next_clause;
                    // }
                    // debug_assert!(!vars[w.blocker.vi()].eliminated); it doesn't hold in TP12
                    if vars.assigned(w.blocker) != LTRUE {
                        let ClauseHead { ref mut lits, .. } = &mut (*head)[w.c];
                        debug_assert!(2 <= lits.len());
                        debug_assert!(lits[0] == false_lit || lits[1] == false_lit);
                        if lits[0] == false_lit {
                            lits.swap(0, 1); // now false_lit is lits[1].
                        }
                        let first = lits[0];
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
                        if first_value == LFALSE {
                            asgs.catchup();
                            // println!("conflict by {} {:?}", cid2fmt(kind.id_from(w.c)), vec2int(&lits));
                            return kind.id_from(w.c);
                        } else {
                            asgs.uncheck_enqueue(vars, first, kind.id_from(w.c));
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
    config: &mut SolverConfiguration,
    cp: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut SolverState,
    vars: &mut [Var],
) -> bool {
    let mut conflict_c = 0.0; // for Luby restart
    let mut a_decision_was_made = false;
    if config.luby_restart {
        config.luby_restart_num_conflict =
            luby(config.luby_restart_inc, config.luby_current_restarts)
                * config.luby_restart_factor;
    }
    loop {
        state.stat[Stat::Propagation as usize] += 1;
        let ci = propagate_fast(asgs, cp, state, vars);
        if ci == NULL_CLAUSE {
            let na = asgs.len();
            let ne = elim.eliminated_vars;
            // println!("na {} + ne {} = {} >= {}", na, ne, na + ne, num_vars);
            if config.num_vars <= na + ne {
                return true;
            }
            // DYNAMIC FORCING RESTART
            if (config.luby_restart && config.luby_restart_num_conflict <= conflict_c)
                || (!config.luby_restart
                    && state.lbd_queue.is_full(LBD_QUEUE_LEN)
                    && ((state.stat[Stat::SumLBD as usize] as f64)
                        / (state.stat[Stat::Conflict as usize] as f64)
                        < state.lbd_queue.average() * config.restart_thr))
            {
                state.stat[Stat::Restart as usize] += 1;
                state.lbd_queue.clear();
                asgs.cancel_until(vars, &mut state.var_order, 0);
                if config.luby_restart {
                    conflict_c = 0.0;
                    config.luby_current_restarts += 1;
                    config.luby_restart_num_conflict =
                        luby(config.luby_restart_inc, config.luby_current_restarts)
                            * config.luby_restart_factor;
                    // println!("luby restart {}", luby_restart_num_conflict);
                }
                // return
            }
            if asgs.level() == 0 {
                cp.simplify(asgs, config, elim, state, vars);
                if !state.ok {
                    return false;
                }
                state.num_solved_vars = asgs.len();
                state.var_order.rebuild(&vars);
            }
            // force_restart();
            if !asgs.remains() {
                let vi = state.var_order.select_var(&vars);
                debug_assert_ne!(vi, 0);
                let p = vars[vi].phase;
                asgs.uncheck_assume(vars, elim, vi.lit(p));
                state.stat[Stat::Decision as usize] += 1;
                a_decision_was_made = true;
            }
        } else {
            conflict_c += 1.0;
            state.stat[Stat::Conflict as usize] += 1;
            let tn_confl = state.stat[Stat::Conflict as usize] as usize; // total number
            if a_decision_was_made {
                a_decision_was_made = false;
            } else {
                state.stat[Stat::NoDecisionConflict as usize] += 1;
            }
            if asgs.level() == config.root_level {
                analyze_final(asgs, config, cp, state, vars, ci, false);
                return false;
            }
            if tn_confl % 5000 == 0 && config.var_decay < config.var_decay_max {
                config.var_decay += 0.01;
            }
            // let real_len = if trail_lim.is_empty() {
            //     trail.len()
            // } else {
            //     trail.len() - trail_lim[0]
            // };
            let real_len = asgs.len();
            state.trail_queue.enqueue(TRAIL_QUEUE_LEN, real_len);
            // DYNAMIC BLOCKING RESTART
            if 100 < tn_confl
                && state.lbd_queue.is_full(LBD_QUEUE_LEN)
                && config.restart_blk * state.trail_queue.average() < (real_len as f64)
            {
                state.lbd_queue.clear();
                state.stat[Stat::BlockRestart as usize] += 1;
            }
            let mut new_learnt: Vec<Lit> = Vec::new();
            let bl = analyze(asgs, config, cp, state, vars, ci, &mut new_learnt);
            // let nas = num_assigns();
            asgs.cancel_until(
                vars,
                &mut state.var_order,
                max(bl as usize, config.root_level),
            );
            if new_learnt.len() == 1 {
                asgs.uncheck_enqueue(vars, new_learnt[0], NULL_CLAUSE);
            } else {
                let lbd = vars.compute_lbd(&new_learnt, &mut state.lbd_temp);
                let v = &mut new_learnt;
                let l0 = v[0];
                let vlen = v.len();
                debug_assert!(0 < lbd);
                let cid = cp.add_clause(config, elim, vars, &mut *v, lbd, tn_confl as f64);
                if lbd <= 2 {
                    state.stat[Stat::NumLBD2 as usize] += 1;
                }
                if vlen == 2 {
                    state.stat[Stat::NumBin as usize] += 1;
                }
                if cid.to_kind() == ClauseKind::Removable as usize {
                    // debug_assert!(!ch.get_flag(ClauseFlag::Dead));
                    // bump_cid(cid);
                    cp[ClauseKind::Removable as usize].bump_activity(
                        cid.to_index(),
                        tn_confl as f64,
                        &mut config.cla_inc,
                    );
                }
                asgs.uncheck_enqueue(vars, l0, cid);
                state.lbd_queue.enqueue(LBD_QUEUE_LEN, lbd);
                state.stat[Stat::SumLBD as usize] += lbd as i64;
            }
            if tn_confl % 10_000 == 0 {
                progress(asgs, config, cp, elim, state, vars, None);
            }
            if tn_confl == 100_000 {
                asgs.cancel_until(vars, &mut state.var_order, 0);
                cp.simplify(asgs, config, elim, state, vars);
                adapt_strategy(config, cp, elim, state, vars);
                // } else if 0 < lbd {
                //     block_restart(lbd, dl, bl, nas);
            }
            // decay_var_activity();
            config.var_inc /= config.var_decay;
            // decay clause activity
            config.cla_inc /= config.cla_decay;
            // glucose reduction
            if state.cur_restart * state.next_reduction <= tn_confl
                || config.glureduce && tn_confl >= state.cur_restart * state.next_reduction
            {
                state.cur_restart =
                    ((tn_confl as f64) / (state.next_reduction as f64)) as usize + 1;
                cp.reduce(elim, state, vars);
                state.next_reduction += config.inc_reduce_db;
            }
            // Since the conflict path pushes a new literal to trail,
            // we don't need to pick up a literal here.
        }
    }
}

#[inline(always)]
fn analyze(
    asgs: &mut AssignStack,
    config: &mut SolverConfiguration,
    cp: &mut ClauseDB,
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
    // let mut last_dl: Vec<Lit> = Vec::new();
    loop {
        // println!("analyze {}", p.int());
        unsafe {
            let ch = clause_mut!(*cp, cid) as *mut ClauseHead;
            debug_assert_ne!(cid, NULL_CLAUSE);
            if cid.to_kind() == (ClauseKind::Removable as usize) {
                // self.bump_cid(cid);
                cp[ClauseKind::Removable as usize].bump_activity(
                    cid.to_index(),
                    state.stat[Stat::Conflict as usize] as f64,
                    &mut config.cla_inc,
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
                //             clause_mut!(*cp, confl).rank = 0
                //         }
                //     }
                // }
            }
            // println!("{}を対応", cid2fmt(cid));
            for q in &(*ch).lits[((p != NULL_LIT) as usize)..] {
                let vi = q.vi();
                let lvl = vars[vi].level;
                // if lvl == 0 {
                //     println!("lvl {}", lvl);
                // }
                debug_assert!(!(*ch).get_flag(ClauseFlag::Dead));
                debug_assert!(
                    !vars[vi].eliminated,
                    format!("analyze assertion: an eliminated var {} occurs", vi)
                );
                // debug_assert!(
                //     vars[vi].assign != BOTTOM,
                //     format!("analyze assertion: unassigned var {:?}", vars[vi])
                // );
                vars[vi].bump_activity(state.stat[Stat::Conflict as usize] as f64);
                state.var_order.update(vars, vi);
                if !state.an_seen[vi] && 0 < lvl {
                    state.an_seen[vi] = true;
                    if dl <= lvl {
                        // println!("{} はレベル{}なのでフラグを立てる", q.int(), lvl);
                        path_cnt += 1;
                    // if vars[vi].reason != NULL_CLAUSE
                    //     && vars[vi].reason.to_kind() == ClauseKind::Removable as usize
                    // {
                    //     last_dl.push(*q);
                    // }
                    } else {
                        // println!("{} はレベル{}なので採用", q.int(), lvl);
                        learnt.push(*q);
                    }
                } else {
                    // if !config.an_seen[vi] {
                    //     println!("{} はもうフラグが立っているので無視", q.int());
                    // } else {
                    //     println!("{} は{}でグラウンドしているので無視", q.int(), lvl);
                    // }
                }
            }
            // set the index of the next literal to ti
            while !state.an_seen[asgs.trail[ti].vi()] {
                // println!("{} はフラグが立ってないので飛ばす", asgs.trail[ti].int());
                ti -= 1;
            }
            p = asgs.trail[ti];
            let next_vi = p.vi();
            cid = vars[next_vi].reason;
            // println!("{} にフラグが立っている。path数は{}, そのreasonは{}", next_vi, path_cnt - 1, cid2fmt(cid));
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
    // println!("最後に{}を採用して{:?}", p.negate().int(), vec2int(learnt));
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
            || !analyze_removable(cp, vars, &mut state.an_seen, *l, &mut to_clear, &level_map)
    });
    if learnt.len() < 30 {
        minimize_with_bi_clauses(cp, vars, &mut state.lbd_temp, learnt);
    }
    // glucose heuristics
    // let lbd = vars.compute_lbd(learnt, lbd_temp);
    // while let Some(l) = last_dl.pop() {
    //     let vi = l.vi();
    //     if clause!(*cp, vars[vi].reason).rank < lbd {
    //         vars[vi].bump_activity(state.stat[Stat::Conflict as usize] as f64);
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
    cp: &mut ClauseDB,
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
        let ch = clause_mut!(*cp, cid);
        if (*ch).lits.len() == 2 && vars.assigned((*ch).lits[0]) == LFALSE {
            (*ch).lits.swap(0, 1);
        }
        for q in &(*ch).lits[1..] {
            let vi = q.vi();
            let lv = vars[vi].level;
            if !an_seen[vi] && 0 < lv {
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
    config: &mut SolverConfiguration,
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

#[inline(always)]
fn adapt_strategy(
    config: &mut SolverConfiguration,
    cps: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut SolverState,
    vars: &mut [Var],
) {
    if !config.adapt_strategy {
        return;
    }
    let mut re_init = false;
    let decpc =
        state.stat[Stat::Decision as usize] as f64 / state.stat[Stat::Conflict as usize] as f64;
    if decpc <= 1.2 {
        config.strategy = SearchStrategy::LowDecisions;
        re_init = true;
    } else if state.stat[Stat::NoDecisionConflict as usize] < 30_000 {
        config.strategy = SearchStrategy::LowSuccesive;
    } else if state.stat[Stat::NoDecisionConflict as usize] > 54_400 {
        config.strategy = SearchStrategy::HighSuccesive;
    } else if state.stat[Stat::NumLBD2 as usize] - state.stat[Stat::NumBin as usize] > 20_000 {
        config.strategy = SearchStrategy::ManyGlues;
    } else {
        config.strategy = SearchStrategy::Generic;
        return;
    }
    match config.strategy {
        SearchStrategy::LowDecisions => {
            config.use_chan_seok = true;
            config.co_lbd_bound = 4;
            config.glureduce = true;
            config.first_reduction = 2000;
            state.next_reduction = 2000;
            state.cur_restart = ((state.stat[Stat::Conflict as usize] as f64
                / state.next_reduction as f64)
                + 1.0) as usize;
            config.inc_reduce_db = 0;
        }
        SearchStrategy::LowSuccesive => {
            config.luby_restart = true;
            config.luby_restart_factor = 100.0;
            config.var_decay = 0.999;
            config.var_decay_max = 0.999;
        }
        SearchStrategy::HighSuccesive => {
            config.use_chan_seok = true;
            config.glureduce = true;
            config.co_lbd_bound = 3;
            config.first_reduction = 30000;
            config.var_decay = 0.99;
            config.var_decay_max = 0.99;
            // randomize_on_restarts = 1;
        }
        SearchStrategy::ManyGlues => {
            config.var_decay = 0.91;
            config.var_decay_max = 0.91;
        }
        _ => (),
    }
    state.ema_asg.reset();
    state.ema_lbd.reset();
    state.lbd_queue.clear();
    state.stat[Stat::SumLBD as usize] = 0;
    state.stat[Stat::Conflict as usize] = 0;
    let [_, learnts, permanents, _] = cps;
    if config.strategy == SearchStrategy::LowDecisions
        || config.strategy == SearchStrategy::HighSuccesive
    {
        // TODO incReduceDB = 0;
        // println!("# Adjusting for low decision levels.");
        // move some clauses with good lbd (col_lbd_bound) to Permanent
        for ch in &mut learnts.head[1..] {
            if ch.get_flag(ClauseFlag::Dead) {
                continue;
            }
            if ch.rank <= config.co_lbd_bound || re_init {
                if ch.rank <= config.co_lbd_bound {
                    permanents.new_clause(&ch.lits, ch.rank);
                }
                learnts.touched[ch.lits[0].negate() as usize] = true;
                learnts.touched[ch.lits[1].negate() as usize] = true;
                ch.flag_on(ClauseFlag::Dead);
            }
        }
        learnts.garbage_collect(vars, elim);
    }
}

// print a progress report
fn progress(
    asgs: &AssignStack,
    config: &mut SolverConfiguration,
    cp: &ClauseDB,
    elim: &Eliminator,
    state: &mut SolverState,
    vars: &[Var],
    mes: Option<&str>,
) {
    if mes != Some("") {
        state.progress_cnt += 1;
    }
    // if self.progress_cnt % 16 == 0 {
    //     self.dump_cnf(format!("G2-p{:>3}.cnf", self.progress_cnt).to_string());
    // }
    let nv = vars.len() - 1;
    let fixed = if asgs.is_zero() {
        asgs.len()
    } else {
        asgs.num_at(0)
    };
    let sum = fixed + elim.eliminated_vars;
    let learnts = &cp[ClauseKind::Removable as usize];
    let good = learnts
        .head
        .iter()
        .skip(1)
        .filter(|c| !c.get_flag(ClauseFlag::Dead) && c.rank <= 3)
        .count();
    if config.use_tty {
        if mes == Some("") {
            println!("{}", state);
            println!();
            println!();
            println!();
            println!();
            println!();
            println!();
        } else {
            print!("\x1B[7A");
            let msg = match mes {
                None => config.strategy.to_str(),
                Some(x) => x,
            };
            println!("{}, State:{:>6}", state, msg,);
            println!(
                "#propagate:{:>14}, #decision:{:>13}, #conflict: {:>12} ",
                state.stat[Stat::Propagation as usize],
                state.stat[Stat::Decision as usize],
                state.stat[Stat::Conflict as usize],
            );
            println!(
                "  Assignment|#rem:{:>9}, #fix:{:>9}, #elm:{:>9}, prog%:{:>8.4} ",
                nv - sum,
                fixed,
                elim.eliminated_vars,
                (sum as f32) / (nv as f32) * 100.0,
            );
            println!(
                "   Clause DB|Remv:{:>9}, good:{:>9}, Perm:{:>9}, Binc:{:>9} ",
                cp[ClauseKind::Removable as usize].count(true),
                good,
                cp[ClauseKind::Permanent as usize].count(true),
                cp[ClauseKind::Binclause as usize].count(true),
            );
            println!(
                "     Restart|#BLK:{:>9}, #RST:{:>9}, emaASG:{:>7.2}, emaLBD:{:>7.2} ",
                state.stat[Stat::BlockRestart as usize],
                state.stat[Stat::Restart as usize],
                state.ema_asg.get(),
                state.ema_lbd.get(),
            );
            println!(
                " Decision Lv|aLBD:{:>9.2}, bjmp:{:>9.2}, cnfl:{:>9.2} |#rdc:{:>9} ",
                state.ema_lbd.slow,
                state.b_lvl.0,
                state.c_lvl.0,
                state.stat[Stat::Reduction as usize],
            );
            println!(
                "  Eliminator|#cls:{:>9}, #var:{:>9},   Clause DB mgr|#smp:{:>9} ",
                elim.clause_queue_len(),
                elim.var_queue_len(),
                state.stat[Stat::Simplification as usize],
            );
        }
    } else if mes == Some("") {
        println!(
            "   #mode,      Variable Assignment      ,,  \
             Clause Database Management  ,,   Restart Strategy      ,, \
             Misc Progress Parameters,,  Eliminator"
        );
        println!(
            "   #init,#remain,#solved,   #elim,total%,,#learnt,(good),  \
             #perm,#binary,,block,force, asgn/,  lbd/,,    lbd, \
             back lv, conf lv,,clause,   var"
        );
    } else {
        let msg = match mes {
            None => config.strategy.to_str(),
            Some(x) => x,
        };
        println!(
            "{:>3}#{:<5},{:>7},{:>7},{:>7},{:>6.3},,{:>7},{:>6},{:>7},\
             {:>7},,{:>5},{:>5}, {:>5.2},{:>6.2},,{:>7.2},{:>8.2},{:>8.2},,\
             {:>6},{:>6}",
            state.progress_cnt,
            msg,
            nv - sum,
            fixed,
            elim.eliminated_vars,
            (sum as f32) / (nv as f32) * 100.0,
            cp[ClauseKind::Removable as usize].count(true),
            good,
            cp[ClauseKind::Permanent as usize].count(true),
            cp[ClauseKind::Binclause as usize].count(true),
            state.stat[Stat::BlockRestart as usize],
            state.stat[Stat::Restart as usize],
            state.ema_asg.get(),
            state.ema_lbd.get(),
            state.ema_lbd.slow,
            state.b_lvl.0,
            state.c_lvl.0,
            elim.clause_queue_len(),
            elim.var_queue_len(),
        );

        // if self.state.progress_cnt == -1 {
        //     self.dump_cnf(format!("test-{}.cnf", self.state.progress_cnt).to_string());
        //     panic!("aa");
        // }
    }
}

#[allow(dead_code)]
fn dump(asgs: &AssignStack, state: &SolverState, str: &str) {
    println!("# {} at {}", str, asgs.level());
    println!(
        "# nassigns {}, decision cands {}",
        asgs.len(),
        state.var_order.len()
    );
    let v = asgs.trail.iter().map(|l| l.int()).collect::<Vec<i32>>();
    let len = asgs.level();
    if 0 < len {
        print!("# - trail[{}]  [", asgs.len());
        let lv0 = asgs.num_at(0);
        if 0 < lv0 {
            print!("0{:?}, ", &asgs.trail[0..lv0]);
        }
        for i in 0..(len - 1) {
            let a = asgs.num_at(i);
            let b = asgs.num_at(i + 1);
            print!("{}{:?}, ", i + 1, &v[a..b]);
        }
        println!("{}{:?}]", len, &v[asgs.num_at(len - 1)..]);
    } else {
        println!("# - trail[  0]  [0{:?}]", &v);
    }
    println!("- trail_lim  {:?}", asgs.trail_lim);
    // println!("{}", self.var_order);
    // self.var_order.check("");
}

#[allow(dead_code)]
fn dump_cnf(
    asgs: &AssignStack,
    config: &SolverConfiguration,
    cps: &ClauseDB,
    vars: &[Var],
    fname: &str,
) {
    for v in vars {
        if v.eliminated {
            if v.assign != BOTTOM {
                panic!("conflicting var {} {}", v.index, v.assign);
            } else {
                println!("eliminate var {}", v.index);
            }
        }
    }
    if let Ok(out) = File::create(&fname) {
        let mut buf = BufWriter::new(out);
        let nv = asgs.len();
        let nc: usize = cps.iter().map(|p| p.head.len() - 1).sum();
        buf.write_all(format!("p cnf {} {}\n", config.num_vars, nc + nv).as_bytes())
            .unwrap();
        let kinds = [
            ClauseKind::Binclause,
            ClauseKind::Removable,
            ClauseKind::Permanent,
        ];
        for kind in &kinds {
            for c in cps[*kind as usize].head.iter().skip(1) {
                for l in &c.lits {
                    buf.write_all(format!("{} ", l.int()).as_bytes()).unwrap();
                }
                buf.write_all(b"0\n").unwrap();
            }
        }
        buf.write_all(b"c from trail\n").unwrap();
        for x in &asgs.trail {
            buf.write_all(format!("{} 0\n", x.int()).as_bytes())
                .unwrap();
        }
    }
}

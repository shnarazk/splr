use crate::clause::{ClauseManagement, GC, *};
use crate::eliminator::{Eliminator, EliminatorIF};
use crate::profiler::*;
use crate::restart::{QueueOperations, RESTART_BLK, RESTART_THR, luby};
use crate::types::*;
use crate::var::{VarOrdering, *};
use std::cmp::max;
use std::collections::VecDeque;
use std::fs;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};

/// For Solver
pub trait SatSolver {
    fn solve(&mut self) -> SolverResult;
    fn build(path: &str) -> (Solver, CNFDescription);
}


/// For Solver
pub trait CDCL {
    /// returns `true` for SAT, `false` for UNSAT.
    fn search(&mut self) -> bool;
    fn propagate(&mut self) -> ClauseId;
    fn propagate_0(&mut self) -> ClauseId;
    fn cancel_until(&mut self, lv: usize) -> ();
    fn enqueue(&mut self, l: Lit, cid: ClauseId) -> bool;
    fn analyze(&mut self, confl: ClauseId, learnt: &mut Vec<Lit>) -> usize;
    fn analyze_final(&mut self, ci: ClauseId, skip_first: bool) -> ();
}

pub const CO_LBD_BOUND: usize = 4;

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

/// stat index
#[derive(Clone, Eq, PartialEq)]
pub enum Stat {
    Conflict = 0,       // the number of backjump
    Decision,           // the number of decision
    Restart,            // the number of restart
    NoDecisionConflict, // the number of 'no decision conflict'
    BlockRestart,       // the number of blacking start
    Propagation,        // the number of propagation
    Reduction,          // the number of reduction
    Simplification,     // the number of simplification
    Assign,             // the number of assigned variables
    SumLBD,
    EndOfStatIndex, // Don't use this dummy.
}

#[derive(Eq, PartialEq)]
pub enum SearchStrategy {
    Generic,
    ChanSeok,
    HighSuccesive,
    LowSuccesive,
    ManyGlues,
}

/// is the collection of all variables.
pub struct Solver {
    /// Configuration
    pub config: SolverConfiguration,
    pub num_vars: usize,
    pub cla_inc: f64,
    pub var_inc: f64,
    pub var_decay: f64,
    pub var_decay_max: f64,
    pub root_level: usize,
    pub strategy: Option<SearchStrategy>,
    /// Variable Assignment Management
    pub vars: Vec<Var>,
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
    /// Variable Order
    pub var_order: VarIdHeap,
    /// Clause Database Management
    pub cp: [ClausePartition; 4],
    pub first_reduction: usize,
    pub next_reduction: usize,
    pub cur_restart: usize,
    pub num_solved_vars: usize,
    pub restart_thr: f64,
    pub restart_blk: f64,
    pub luby_restart: bool,
    pub luby_restart_num_conflict: f64,
    pub luby_restart_inc: f64,
    pub luby_current_restarts: usize,
    pub luby_restart_factor: f64,
    /// Variable Elimination
    pub eliminator: Eliminator,
    /// Working memory
    pub ok: bool,
    pub model: Vec<Lbool>,
    pub conflicts: Vec<Lit>,
    pub stat: Vec<i64>,
    pub profile: Profile,
    pub an_seen: Vec<bool>,
    pub lbd_temp: Vec<usize>,
    /// restart heuristics
    pub lbd_queue: VecDeque<usize>,
    pub trail_queue: VecDeque<usize>,
    pub ema_asg: Ema2,
    pub ema_lbd: Ema2,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub next_restart: u64,
    pub restart_exp: f64,
    pub progress_cnt: i64,
}

const LBD_QUEUE_LEN: usize = 50;
const TRAIL_QUEUE_LEN: usize = 5000;

impl Solver {
    pub fn new(cfg: SolverConfiguration, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let path = &cnf.pathname;
        let (_fe, se) = cfg.ema_coeffs;
        let re = cfg.restart_expansion;
        let vdr = cfg.variable_decay_rate;
        let sve = cfg.use_sve;
        Solver {
            config: cfg,
            num_vars: nv,
            cla_inc: 1.0,
            var_inc: vdr,
            var_decay: VAR_DECAY,
            var_decay_max: MAX_VAR_DECAY,
            root_level: 0,
            strategy: None,
            vars: Var::new_vars(nv),
            trail: Vec::with_capacity(nv),
            trail_lim: Vec::new(),
            q_head: 0,
            var_order: VarIdHeap::new(nv, nv),
            cp: [
                ClausePartition::build(ClauseKind::Liftedlit, nv, 0),
                ClausePartition::build(ClauseKind::Removable, nv, nc),
                ClausePartition::build(ClauseKind::Permanent, nv, 256),
                ClausePartition::build(ClauseKind::Binclause, nv, 256),
            ],
            first_reduction: 1000,
            next_reduction: 1000,
            cur_restart: 1,
            num_solved_vars: 0,
            restart_thr: RESTART_THR,
            restart_blk: RESTART_BLK,
            luby_restart: false,
            luby_restart_num_conflict: 0.0,
            luby_restart_inc: 2.0,
            luby_current_restarts: 0,
            luby_restart_factor: 100.0,
            eliminator: Eliminator::new(sve),
            ok: true,
            model: vec![BOTTOM; nv + 1],
            conflicts: vec![],
            stat: vec![0; Stat::EndOfStatIndex as usize],
            profile: Profile::new(&path.to_string()),
            an_seen: vec![false; nv + 1],
            lbd_temp: vec![0; nv + 1],
            lbd_queue: VecDeque::new(),
            trail_queue: VecDeque::new(),
            ema_asg: Ema2::new(3.8, 50_000.0),   // for blocking 4
            ema_lbd: Ema2::new(160.0, 50_000.0), // for forcing 160
            b_lvl: Ema::new(se),
            c_lvl: Ema::new(se),
            next_restart: 100,
            restart_exp: re,
            progress_cnt: 0,
        }
    }
    // print a progress report
    pub fn progress(&mut self, mes: &str) {
        self.progress_cnt += 1;
        // if self.progress_cnt % 16 == 0 {
        //     self.dump_cnf(format!("G2-p{:>3}.cnf", self.progress_cnt).to_string());
        // }
        let nv = self.vars.len() - 1;
        let fixed = if self.trail_lim.is_empty() {
            self.trail.len()
        } else {
            self.trail_lim[0]
        };
        let sum = fixed + self.eliminator.eliminated_vars;
        let learnts = &self.cp[ClauseKind::Removable as usize];
        let good = learnts
            .head
            .iter()
            .skip(1)
            .filter(|c| !c.get_flag(ClauseFlag::Dead) && c.rank <= 3)
            .count();
        if self.config.use_tty {
            if mes.is_empty() {
                println!("{}", self.profile);
                println!();
                println!();
                println!();
                println!();
                println!();
                println!();
            } else {
                print!("\x1B[7A");
                println!("{}, State:{:>6}", self.profile, mes,);
                println!(
                    "#propagate:{:>14}, #decision:{:>13}, #conflict: {:>12}",
                    self.stat[Stat::Propagation as usize],
                    self.stat[Stat::Decision as usize],
                    self.stat[Stat::Conflict as usize],
                );
                println!(
                    "  Assignment|#rem:{:>9}, #fix:{:>9}, #elm:{:>9}, prog%:{:>8.4}",
                    nv - sum,
                    fixed,
                    self.eliminator.eliminated_vars,
                    (sum as f32) / (nv as f32) * 100.0,
                );
                println!(
                    "   Clause DB|Remv:{:>9}, good:{:>9}, Perm:{:>9}, Binc:{:>9}",
                    self.cp[ClauseKind::Removable as usize]
                        .head
                        .iter()
                        .skip(1)
                        .filter(|c| !c.get_flag(ClauseFlag::Dead))
                        .count(),
                    good,
                    self.cp[ClauseKind::Permanent as usize]
                        .head
                        .iter()
                        .skip(1)
                        .filter(|c| !c.get_flag(ClauseFlag::Dead))
                        .count(),
                    self.cp[ClauseKind::Binclause as usize]
                        .head
                        .iter()
                        .skip(1)
                        .filter(|c| !c.get_flag(ClauseFlag::Dead))
                        .count(),
                );
                println!(
                    "     Restart|#BLK:{:>9}, #RST:{:>9}, emaASG:{:>7.2}, emaLBD:{:>7.2}",
                    self.stat[Stat::BlockRestart as usize],
                    self.stat[Stat::Restart as usize],
                    self.ema_asg.get(),
                    self.ema_lbd.get(),
                );
                println!(
                    " Decision Lv|aLBD:{:>9.2}, bjmp:{:>9.2}, cnfl:{:>9.2} |#rdc:{:>9}",
                    self.ema_lbd.slow,
                    self.b_lvl.0,
                    self.c_lvl.0,
                    self.stat[Stat::Reduction as usize],
                );
                println!(
                    "  Eliminator|#cls:{:>9}, #var:{:>9},   Clause DB mgr|#smp:{:>9}",
                    self.eliminator.clause_queue_len(),
                    self.eliminator.var_queue_len(),
                    self.stat[Stat::Simplification as usize],
                );
            }
        } else if mes.is_empty() {
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
                println!(
                    "{:>3}#{:<5},{:>7},{:>7},{:>7},{:>6.3},,{:>7},{:>6},{:>7},\
                     {:>7},,{:>5},{:>5}, {:>5.2},{:>6.2},,{:>7.2},{:>8.2},{:>8.2},,\
                     {:>6},{:>6}",
                    self.progress_cnt,
                    mes,
                    nv - sum,
                    fixed,
                    self.eliminator.eliminated_vars,
                    (sum as f32) / (nv as f32) * 100.0,
                    self.cp[ClauseKind::Removable as usize]
                        .head
                        .iter()
                        .skip(1)
                        .filter(|c| !c.get_flag(ClauseFlag::Dead))
                        .count(),
                    good,
                    self.cp[ClauseKind::Permanent as usize]
                        .head
                        .iter()
                        .skip(1)
                        .filter(|c| !c.get_flag(ClauseFlag::Dead))
                        .count(),
                    self.cp[ClauseKind::Binclause as usize]
                        .head
                        .iter()
                        .skip(1)
                        .filter(|c| !c.get_flag(ClauseFlag::Dead))
                        .count(),
                    self.stat[Stat::BlockRestart as usize],
                    self.stat[Stat::Restart as usize],
                    self.ema_asg.get(),
                    self.ema_lbd.get(),
                    self.ema_lbd.slow,
                    self.b_lvl.0,
                    self.c_lvl.0,
                    self.eliminator.clause_queue_len(),
                    self.eliminator.var_queue_len(),
                );
            }

        // if self.progress_cnt == -1 {
        //     self.dump_cnf(format!("test-{}.cnf", self.progress_cnt).to_string());
        //     panic!("aa");
        // }
    }

    pub fn num_assigns(&self) -> usize {
        self.trail.len()
    }

    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    pub fn adapt_strategy(&mut self) {
        let mut re_init = false;
        let decpc =
            self.stat[Stat::Decision as usize] as f64 / self.stat[Stat::Conflict as usize] as f64;
        if decpc <= 1.2 {
            self.strategy = Some(SearchStrategy::ChanSeok);
        } else if self.stat[Stat::NoDecisionConflict as usize] < 30_000 {
            self.strategy = Some(SearchStrategy::LowSuccesive);
        } else if self.stat[Stat::NoDecisionConflict as usize] > 54_400 {
            self.strategy = Some(SearchStrategy::HighSuccesive);
        } else {
            self.strategy = Some(SearchStrategy::Generic);
            return;
        }
        if self.strategy != None {
            self.ema_asg.reset();
            self.ema_lbd.reset();
            // conflictsRestarts = 0;
            match self.strategy {
                Some(SearchStrategy::ChanSeok) => {
                    re_init = true;
                    let _glureduce = true;
                    self.first_reduction = 2000;
                    self.next_reduction = 2000;
                    self.cur_restart = ((self.stat[Stat::Conflict as usize] as f64
                        / self.next_reduction as f64)
                        + 1.0) as usize;
                    // TODO incReduceDB = 0;
                    // println!("# Adjusting for low decision levels.");
                    // move some clauses with good lbd (col_lbd_bound) to Permanent
                    let [_, ref mut learnts, ref mut permanents, _] = self.cp;
                    for ch in &mut learnts.head[1..] {
                        if ch.get_flag(ClauseFlag::Dead) {
                            continue;
                        }
                        if ch.rank <= CO_LBD_BOUND {
                            // ch.lits.insert(0, ch.lit[0]);
                            learnts.touched[ch.lit[0].negate() as usize] = true;
                            // ch.lits.insert(1, ch.lit[1]);
                            learnts.touched[ch.lit[1].negate() as usize] = true;
                            permanents.new_clause(
                                &ch.lits,
                                ch.rank,
                                ch.get_flag(ClauseFlag::Locked),
                            );
                            ch.set_flag(ClauseFlag::Dead, true);
                        }
                    }
                    learnts.garbage_collect(&mut self.vars, &mut self.eliminator);
                }
                Some(SearchStrategy::HighSuccesive) => {
                    // coLBDBound = 3;
                    // firstReduceDB = 30000;
                    self.var_decay = 0.99;
                    self.var_decay_max = 0.99;
                    // randomize_on_restarts = 1;
                    // adjusted = true;

                }
                Some(SearchStrategy::LowSuccesive) => {
                    // This path needs Luby
                    self.luby_restart = true;
                    // luby_restart_factor = 100;
                    self.var_decay = 0.999;
                    self.var_decay_max = 0.999;
                    // adjusted = true;
                }
                Some(SearchStrategy::ManyGlues) => {
                    self.var_decay = 0.91;
                    self.var_decay_max = 0.91;
                    // adjusted = true;
                }
                Some(SearchStrategy::Generic) => {
                    // ??
                }
                None => {
                    //
                }
            }                                        
        }
        if re_init {
            // make all claueses garbage
        }
    }
}

impl SatSolver for Solver {
    fn solve(&mut self) -> SolverResult {
        if !self.ok {
            return Ok(Certificate::UNSAT(Vec::new()));
        }
        // TODO: deal with assumptions
        // s.root_level = 0;
        self.num_solved_vars = self.trail.len();
        self.progress("");
        // self.eliminator.use_elim = true;
        self.eliminator.var_queue.clear();
        if self.eliminator.use_elim {
            for v in &mut self.vars[1..] {
                if v.neg_occurs.is_empty() && !v.pos_occurs.is_empty() && v.assign == BOTTOM {
                    debug_assert!(!v.eliminated);
                    debug_assert!(!self.trail.contains(&v.index.lit(LTRUE)));
                    debug_assert!(!self.trail.contains(&v.index.lit(LFALSE)));
                    v.assign = LTRUE;
                    self.trail.push(v.index.lit(LTRUE));
                } else if v.pos_occurs.is_empty() && !v.neg_occurs.is_empty() && v.assign == BOTTOM {
                    debug_assert!(!v.eliminated);
                    debug_assert!(!self.trail.contains(&v.index.lit(LTRUE)));
                    debug_assert!(!self.trail.contains(&v.index.lit(LFALSE)));
                    v.assign = LFALSE;
                    self.trail.push(v.index.lit(LFALSE));
                } else if v.pos_occurs.len() == 1 || v.neg_occurs.len() == 1 {
                    self.eliminator.enqueue_var(v);
                }
            }
            self.progress("load");
            self.simplify();
            self.progress("simp");
        } else {
            self.progress("load");
        }
        // self.config.use_sve = false;
        // self.eliminator.use_elim = false;
        self.stat[Stat::Simplification as usize] += 1;
        match self.search() {
            _ if !self.ok => {
                self.cancel_until(0);
                self.progress("error");
                Err(SolverException::InternalInconsistent)
            }
            true => {
                self.progress("SAT");
                let mut result = Vec::new();
                for vi in 1..=self.num_vars {
                    match self.vars[vi].assign {
                        LTRUE => result.push(vi as i32),
                        LFALSE => result.push(0 - vi as i32),
                        _ => result.push(0),
                    }
                }
                if self.eliminator.use_elim {
                    self.extend_model(&mut result);
                }
                self.cancel_until(0);
                Ok(Certificate::SAT(result))
            }
            false => {
                self.progress("UNSAT");
                self.cancel_until(0);
                let mut v = Vec::new();
                for l in &self.conflicts {
                    v.push(l.int());
                }
                Ok(Certificate::UNSAT(v))
            }
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
        let mut s: Solver = Solver::new(SolverConfiguration::default(), &cnf);
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
                        s.ok = false;
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(s.vars.len() - 1, cnf.num_of_variables);
        (s, cnf)
    }
}

impl CDCL for Solver {
    fn propagate(&mut self) -> ClauseId {
        let Solver {
            ref mut vars,
            ref mut cp,
            ref mut trail,
            ref trail_lim,
            ref mut q_head,
            ref mut stat,
            ..
        } = self;
        while *q_head < trail.len() {
            let p: usize = trail[*q_head] as usize;
            let false_lit = (p as Lit).negate();
            *q_head += 1;
            stat[Stat::Propagation as usize] += 1;
            let kinds = [
                ClauseKind::Binclause,
                ClauseKind::Removable,
                ClauseKind::Permanent,
            ];
            for kind in &kinds {
                // cp[*kind as usize].check(false_lit);
                let head = &mut cp[*kind as usize].head[..];
                let watcher = &mut cp[*kind as usize].watcher[..];
                unsafe
                {
                    let mut pre = &mut (*watcher)[p] as *mut usize;
                    'next_clause: while *pre != NULL_CLAUSE {
                        let ch = &mut (*head)[*pre];
                        debug_assert!((*ch).lit[0] == false_lit || (*ch).lit[1] == false_lit);
                        let my_index = ((*ch).lit[0] != false_lit) as usize;
                        {
                            // Handling a special case for simplify
                            // check other's aliveness
                            let other = (*ch).lit[(my_index == 0) as usize];
                            debug_assert!(!vars[other.vi()].eliminated);
                        }
                        let other_value = vars.assigned((*ch).lit[(my_index == 0) as usize]);
                        if other_value != LTRUE {
                            debug_assert!(2 <= (*ch).lits.len());
                            debug_assert!((*ch).lits[0] == false_lit || (*ch).lits[1] == false_lit);
                            if (*ch).lits[0] == false_lit {
                                (*ch).lits.swap(0, 1); // now false_lit is lits[1].
                            }
                            for (k, lk) in (*ch).lits.iter().enumerate().skip(2) {
                                // below is equivalent to 'assigned(lk) != LFALSE'
                                if (((lk & 1) as u8) ^ vars[lk.vi()].assign) != 0 {
                                    let cix = *pre;
                                    *pre = (*ch).next_watcher[my_index];
                                    let alt = &mut (*watcher)[lk.negate() as usize];
                                    (*ch).next_watcher[my_index] = *alt;
                                    *alt = cix;
                                    (*ch).lit[my_index] = *lk;
                                    debug_assert!((*ch).lits[1] == false_lit);
                                    (*ch).lits[1] = *lk;
                                    (*ch).lits[k] = false_lit; // Don't move this above (needed by enumerate)
                                    continue 'next_clause;
                                }
                            }
                            if other_value == LFALSE {
                                *q_head = trail.len();
                                return kind.id_from(*pre);
                            } else {
                                // self.uncheck_enqueue(other, kind.id_from((*c).index));
                                let dl = trail_lim.len();
                                let other = (*ch).lits[0];
                                // println!("unchecked_enqueue embedded into propagate {}", other.int());
                                let v = &mut vars[other.vi()];
                                debug_assert!(v.assign == other.lbool() || v.assign == BOTTOM);
                                v.assign = other.lbool();
                                v.level = dl;
                                debug_assert!(*pre != NULL_CLAUSE);
                                if dl == 0 {
                                    v.reason = NULL_CLAUSE;
                                } else {
                                    v.reason = kind.id_from(*pre);
                                    (*ch).set_flag(ClauseFlag::Locked, true);
                                }
                                debug_assert!(!v.eliminated);
                                // debug_assert!(!trail.contains(&other));
                                // debug_assert!(!trail.contains(&other.negate()));
                                trail.push(other);
                            }
                        }
                        pre = &mut (*ch).next_watcher[my_index];
                    }
                }
            }
        }
        NULL_CLAUSE
    }

    /// for eliminater invoked by simplify
    fn propagate_0(&mut self) -> ClauseId {
        let Solver {
            ref mut vars,
            ref mut cp,
            ref mut trail,
            ref trail_lim,
            ref mut q_head,
            ref mut stat,
            ..
        } = self;
        while *q_head < trail.len() {
            let p: usize = trail[*q_head] as usize;
            let false_lit = (p as Lit).negate();
            *q_head += 1;
            stat[Stat::Propagation as usize] += 1;
            let kinds = [
                ClauseKind::Binclause,
                ClauseKind::Removable,
                ClauseKind::Permanent,
            ];
            for kind in &kinds {
                // cp[*kind as usize].check(false_lit);
                unsafe {
                    let head = &mut cp[*kind as usize].head[..] as *mut [ClauseHead];
                    let watcher = &mut cp[*kind as usize].watcher[..] as *mut [ClauseIndex];
                    let mut pre = &mut (*watcher)[p] as *mut usize;
                    'next_clause: while *pre != NULL_CLAUSE {
                        let ch = &mut (*head)[*pre] as *mut ClauseHead;
                        debug_assert!((*ch).lit[0] == false_lit || (*ch).lit[1] == false_lit);
                        let my_index = ((*ch).lit[0] != false_lit) as usize;
                        // let ch = &mut (*body)[*pre] as *mut ClauseBody;
                        {
                            // Handling a special case for simplify
                            if (*ch).get_flag(ClauseFlag::Dead) {
                                pre = &mut (*ch).next_watcher[my_index];
                                continue 'next_clause;
                            }
                            // check other's aliveness
                            let other = (*ch).lit[(my_index == 0) as usize];
                            debug_assert!(!vars[other.vi()].eliminated);
                        }
                        let other_value = vars.assigned((*ch).lit[(my_index == 0) as usize]);
                        if other_value != LTRUE {
                            debug_assert!(2 <= (*ch).lits.len());
                            debug_assert!((*ch).lits[0] == false_lit || (*ch).lits[1] == false_lit);
                            if (*ch).lits[0] == false_lit {
                                (*ch).lits.swap(0, 1); // now false_lit is lits[1].
                            }
                            for (k, lk) in (*ch).lits.iter().enumerate().skip(2) {
                                // below is equivalent to 'assigned(lk) != LFALSE'
                                debug_assert!(1 < *lk);
                                debug_assert!(!vars[lk.vi()].eliminated);
                                if (((lk & 1) as u8) ^ vars[lk.vi()].assign) != 0 {
                                    let cix = *pre;
                                    *pre = (*ch).next_watcher[my_index];
                                    let alt = &mut (*watcher)[lk.negate() as usize];
                                    (*ch).next_watcher[my_index] = *alt;
                                    *alt = cix;
                                    (*ch).lit[my_index] = *lk;
                                    debug_assert!((*ch).lits[1] == false_lit);
                                    (*ch).lits[1] = *lk;
                                    (*ch).lits[k] = false_lit;
                                    continue 'next_clause;
                                }
                            }
                            if other_value == LFALSE {
                                *q_head = trail.len();
                                return kind.id_from(*pre);
                            } else {
                                // self.uncheck_enqueue(other, kind.id_from((*c).index));
                                let dl = trail_lim.len();
                                debug_assert!(dl == 0);
                                let other = (*ch).lits[0];
                                let v = &mut vars[other.vi()];
                                debug_assert!(v.assign == other.lbool() || v.assign == BOTTOM);
                                v.assign = other.lbool();
                                v.level = dl;
                                debug_assert!(*pre != NULL_CLAUSE);
                                v.reason = NULL_CLAUSE;
                                debug_assert!(!v.eliminated);
                                // debug_assert!(!trail.contains(&other));debug_
                                // debug_assert!(!trail.contains(&other.negate()));
                                trail.push(other);
                            }
                        }
                        pre = &mut (*ch).next_watcher[my_index];
                    }
                }
            }
        }
        NULL_CLAUSE
    }

    /// main loop
    fn search(&mut self) -> bool {
        let mut conflict_c = 0.0;  // for Luby restart
        let mut a_decision_was_made = false;
        if self.luby_restart {
            self.luby_restart_num_conflict = luby(self.luby_restart_inc, self.luby_current_restarts) * self.luby_restart_factor;
        }
        let root_lv = self.root_level;
        loop {
            self.stat[Stat::Propagation as usize] += 1;
            let ci = self.propagate();
            if ci == NULL_CLAUSE {
                let na = self.num_assigns();
                let ne = self.eliminator.eliminated_vars;
                // println!("na {} + ne {} = {} >= {}", na, ne, na + ne, self.num_vars);
                if self.num_vars <= na + ne {
                    // let mut cnt = 0;
                    // for v in &self.vars {
                    //     if v.eliminated {
                    //         cnt += 1;
                    //     }
                    // }
                    // debug_assert_eq!(cnt, self.eliminator.eliminated_vars);
                    return true;
                }
                // DYNAMIC FORCING RESTART
                if (self.luby_restart && self.luby_restart_num_conflict <= conflict_c)
                    || (!self.luby_restart
                        && self.lbd_queue.is_full(LBD_QUEUE_LEN)
                        && ((self.stat[Stat::SumLBD as usize] as f64)
                            / (self.stat[Stat::Conflict as usize] as f64)
                            < self.lbd_queue.average() * self.restart_thr))
                {
                    self.stat[Stat::Restart as usize] += 1;
                    self.lbd_queue.clear();
                    self.cancel_until(0);

                    if self.luby_restart {
                        conflict_c = 0.0;
                        self.luby_current_restarts += 1;
                        self.luby_restart_num_conflict = luby(self.luby_restart_inc, self.luby_current_restarts) * self.luby_restart_factor;
                        // println!("luby restart {}", self.luby_restart_num_conflict);
                    }
                    // return
                }
                if self.decision_level() == 0 {
                    self.simplify();
                    if !self.ok {
                        return false;
                    }
                    self.num_solved_vars = self.num_assigns();
                    self.rebuild_heap();
                }
                // self.force_restart();
                if self.trail.len() <= self.q_head {
                    // let na = self.num_assigns();
                    // let ne = self.eliminator.eliminated_vars;
                    // // println!("na {} + ne {} = {} , {}", na, ne, na + ne, self.num_vars);
                    // if na + ne >= self.num_vars {
                    //     panic!("na {} + ne {}", na, ne);
                    // }
                    let vi = self.select_var();
                    debug_assert_ne!(vi, 0);
                    let p = self.vars[vi].phase;
                    self.uncheck_assume(vi.lit(p));
                    self.stat[Stat::Decision as usize] += 1;
                    a_decision_was_made = true;
                }
            } else {
                conflict_c += 1.0;
                self.stat[Stat::Conflict as usize] += 1;
                if a_decision_was_made {
                    a_decision_was_made = false;
                } else {
                    self.stat[Stat::NoDecisionConflict as usize] += 1;
                }
                let dl = self.decision_level();
                if dl == self.root_level {
                    self.analyze_final(ci, false);
                    return false;
                }
                if self.stat[Stat::Conflict as usize] % 5000 == 0
                    && self.var_decay < self.var_decay_max
                {
                    self.var_decay += 0.01;
                }
                // let real_len = if self.trail_lim.is_empty() {
                //     self.trail.len()
                // } else {
                //     self.trail.len() - self.trail_lim[0]
                // };
                let real_len = self.trail.len();
                self.trail_queue.enqueue(TRAIL_QUEUE_LEN, real_len);
                // DYNAMIC BLOCKING RESTART
                let count = self.stat[Stat::Conflict as usize] as u64;
                if 100 < count
                    && self.lbd_queue.is_full(LBD_QUEUE_LEN)
                    && self.restart_blk * self.trail_queue.average() < (real_len as f64)
                {
                    self.lbd_queue.clear();
                    self.stat[Stat::BlockRestart as usize] += 1;
                }
                let mut new_learnt: Vec<Lit> = Vec::new();
                let bl = self.analyze(ci, &mut new_learnt);
                // let nas = self.num_assigns();
                self.cancel_until(max(bl as usize, root_lv));
                let lbd;
                if new_learnt.len() == 1 {
                    let l = new_learnt[0];
                    self.uncheck_enqueue(l, NULL_CLAUSE);
                    lbd = 1;
                } else {
                    lbd = self.vars.compute_lbd(&new_learnt, &mut self.lbd_temp);
                    let v = &mut new_learnt;
                    let l0 = v[0];
                    debug_assert!(0 < lbd);
                    let cid = self.add_clause(&mut *v, lbd);
                    if cid.to_kind() == ClauseKind::Removable as usize {
                        // clause_body_mut!(self.cp, cid).set_flag(ClauseFlag::JustUsed, true);
                        // debug_assert!(!ch.get_flag(ClauseFlag::Dead));
                        // self.bump_cid(cid);
                        self.cp[ClauseKind::Removable as usize].bump_activity(
                            cid.to_index(),
                            self.stat[Stat::Conflict as usize] as f64,
                            &mut self.cla_inc,
                        );
                    }
                    self.uncheck_enqueue(l0, cid);
                    clause_mut!(self.cp, cid).set_flag(ClauseFlag::Locked, true);
                }
                self.stat[Stat::SumLBD as usize] += lbd as i64;
                self.lbd_queue.enqueue(LBD_QUEUE_LEN, lbd);
                if self.stat[Stat::Conflict as usize] % 10_000 == 0 {
                    self.progress(match self.strategy {
                        None => "none",
                        Some(SearchStrategy::Generic) => "defl",
                        Some(SearchStrategy::ChanSeok) => "Chan",
                        Some(SearchStrategy::HighSuccesive) => "High",
                        Some(SearchStrategy::LowSuccesive) => "LowS",
                        Some(SearchStrategy::ManyGlues) => "Many",
                    });
                }
                if self.stat[Stat::Conflict as usize] == 100_000 {
                    self.cancel_until(0);
                    self.simplify();
                    // self.rebuild_heap();
                    self.adapt_strategy();
                    // } else if 0 < lbd {
                    //     self.block_restart(lbd, dl, bl, nas);
                }

                // self.decay_var_activity();
                // decay clause activity
                self.cla_inc /= self.config.clause_decay_rate;
                // glucose reduction
                let conflicts = self.stat[Stat::Conflict as usize] as usize;
                if self.cur_restart * self.next_reduction <= conflicts {
                    self.cur_restart =
                        ((conflicts as f64) / (self.next_reduction as f64)) as usize + 1;
                    self.reduce();
                }
                // Since the conflict path pushes a new literal to trail,
                // we don't need to pick up a literal here.
            }
        }
    }

    fn cancel_until(&mut self, lv: usize) {
        let Solver {
            ref mut cp,
            ref mut vars,
            ref mut trail, ref mut trail_lim,
            ref mut var_order,
            ref mut q_head,
            ..
        } = self;
        if trail_lim.len() <= lv {
            return;
        }
        let lim = trail_lim[lv];
        for l in &trail[lim..] {
            // println!("cancel_until {}", l.int());
            let vi = l.vi();
            let v = &mut vars[vi];
            v.phase = v.assign;
            v.assign = BOTTOM;
            if v.reason != NULL_CLAUSE {
                clause_mut!(*cp, v.reason).set_flag(ClauseFlag::Locked, false);
                v.reason = NULL_CLAUSE;
            }
            var_order.insert(vars, vi);
        }
        trail.truncate(lim);
        trail_lim.truncate(lv);
        *q_head = lim;
    }

    /// returns `false` if an conflict occures.
    fn enqueue(&mut self, l: Lit, cid: ClauseId) -> bool {
        let sig = l.lbool();
        let val = self.vars[l.vi()].assign;
        let dl = self.decision_level();
        if val == BOTTOM {
            let v = &mut self.vars[l.vi()];
            debug_assert!(!v.eliminated);
            v.assign = sig;
            // if dl == 0 && cid != NULL_CLAUSE {
            //     println!("enqueue {}", cid2fmt(cid));
            // }
            v.reason = cid;
            if dl == 0 {
                // if !v.enqueued {
                //     self.eliminator.var_queue.push(l.vi());
                //     v.enqueued = true;
                // }
                v.reason = NULL_CLAUSE;
                v.activity = 0.0;
            }
            v.level = dl;
            if cid != NULL_CLAUSE {
                clause_mut!(self.cp, cid).set_flag(ClauseFlag::Locked, true);
            }
            if dl == 0 {
                self.var_order.remove(&self.vars, l.vi());
            }
            // debug_assert!(!self.trail.contains(&l));
            // debug_assert!(!self.trail.contains(&l.negate()));
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }

    fn analyze(&mut self, confl: ClauseId, learnt: &mut Vec<Lit>) -> usize {
        learnt.push(0);
        let dl = self.decision_level();
        let mut cid: usize = confl;
        let mut p = NULL_LIT;
        let mut ti = self.trail.len() - 1; // trail index
        let mut path_cnt = 0;
        // let mut last_dl: Vec<Lit> = Vec::new();
        loop {
            // println!("analyze {}", p.int());
            unsafe {
                let ch = clause_mut!(self.cp, cid) as *mut ClauseHead;
                debug_assert_ne!(cid, NULL_CLAUSE);
                if cid.to_kind() == (ClauseKind::Removable as usize) {
                    // self.bump_cid(cid);
                    self.cp[ClauseKind::Removable as usize].bump_activity(
                        cid.to_index(),
                        self.stat[Stat::Conflict as usize] as f64,
                        &mut self.cla_inc,
                    );
                    // if 2 < (*ch).rank {
                    //     let nblevels = compute_lbd(&self.vars, &ch.lits, &mut self.lbd_temp);
                    //     if nblevels + 1 < (*ch).rank {
                    //         (*ch).rank = nblevels;
                    //         if nblevels <= 30 {
                    //             (*ch).set_flag(ClauseFlag::JustUsed, true);
                    //         }
                    //         if self.strategy == Some(SearchStrategy::ChanSeok)
                    //             && nblevels < CO_LBD_BOUND
                    //         {
                    //             (*ch).rank = 0;
                    //             clause_body_mut!(self.cp, confl).rank = 0
                    //         }
                    //     }
                    // }
                }
                // println!("{}を対応", cid2fmt(cid));
                for q in &(*ch).lits[((p != NULL_LIT) as usize)..] {
                    let vi = q.vi();
                    let lvl = self.vars[vi].level;
                    // if lvl == 0 {
                    //     println!("lvl {}", lvl);
                    // }
                    debug_assert!(!(*ch).get_flag(ClauseFlag::Dead));
                    debug_assert!(
                        !self.vars[vi].eliminated,
                        format!("analyze assertion: an eliminated var {} occurs", vi)
                    );
                    // debug_assert!(
                    //     self.vars[vi].assign != BOTTOM,
                    //     format!("analyze assertion: unassigned var {:?}", self.vars[vi])
                    // );
                    self.vars[vi].bump_activity(self.stat[Stat::Conflict as usize] as f64);
                    self.var_order.update(&self.vars, vi);
                    if !self.an_seen[vi] && 0 < lvl {
                        self.an_seen[vi] = true;
                        if dl <= lvl {
                            // println!("{} はレベル{}なのでフラグを立てる", q.int(), lvl);
                            path_cnt += 1;
                            // if self.vars[vi].reason != NULL_CLAUSE
                            //     && self.vars[vi].reason.to_kind() == ClauseKind::Removable as usize
                            // {
                            //     last_dl.push(*q);
                            // }
                        } else {
                            // println!("{} はレベル{}なので採用 {}", q.int(), lvl, dl);
                            learnt.push(*q);
                        }
                    } else {
                        // println!("{} はもうフラグが立っているかグラウンドしている{}ので無視", q.int(), lvl);
                    }
                }
                // set the index of the next literal to ti
                while !self.an_seen[self.trail[ti].vi()] {
                    // println!("{} はフラグが立ってないので飛ばす", self.trail[ti].int());
                    ti -= 1;
                }
                p = self.trail[ti];
                let next_vi = p.vi();
                cid = self.vars[next_vi].reason;
                // println!("{} にフラグが立っている。そのpath数は{}, \
                //           そのreason{}を探索", next_vi, path_cnt - 1, cid2fmt(cid));
                self.an_seen[next_vi] = false;
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
        // println!(
        //     "最後に{}を採用して{:?}",
        //     p.negate().int(), vec2int(learnt)
        // );
        // simplify phase
        let mut to_clear = Vec::new();
        to_clear.push(p.negate());
        let mut level_map = vec![false; self.decision_level()+1];
        for l in &learnt[1..] {
            to_clear.push(*l);
            level_map[self.vars[l.vi()].level] = true;
        }
        learnt.retain(|l| self.vars[l.vi()].reason == NULL_CLAUSE || !self.analyze_removable(*l, &mut to_clear, &level_map));
        if learnt.len() < 30 {
            self.minimize_with_bi_clauses(learnt);
        }
        // glucose heuristics
        // let lbd = self.vars.compute_lbd(learnt, &mut self.lbd_temp);
        // while let Some(l) = last_dl.pop() {
        //     let vi = l.vi();
        //     if clause!(self.cp, self.vars[vi].reason).rank < lbd {
        //         self.vars[vi].bump_activity(self.stat[Stat::Conflict as usize] as f64);
        //         self.var_order.update(&self.vars, vi);
        //     }
        // }
        // find correct backtrack level from remaining literals
        let mut level_to_return = 0;
        if 1 < learnt.len() {
            let mut max_i = 1;
            level_to_return = self.vars[learnt[max_i].vi()].level;
            // for i in 2..learnt.len() {
            for (i, l) in learnt.iter().enumerate().skip(2) {
                let lv = self.vars[l.vi()].level;
                if level_to_return < lv {
                    level_to_return = lv;
                    max_i = i;
                }
            }
            learnt.swap(1, max_i);
        }
        for l in &to_clear {
            self.an_seen[l.vi()] = false;
        }
        level_to_return
    }

    fn analyze_final(&mut self, ci: ClauseId, skip_first: bool) {
        let mut seen = vec![false; self.num_vars + 1];
        self.conflicts.clear();
        if self.root_level != 0 {
            let ch = clause!(self.cp, ci);
            for l in &ch.lits[skip_first as usize..] {
                let vi = l.vi();
                if 0 < self.vars[vi].level {
                    self.an_seen[vi] = true;
                }
            }
            let tl0 = self.trail_lim[0];
            let start = if self.trail_lim.len() <= self.root_level {
                self.trail.len()
            } else {
                self.trail_lim[self.root_level]
            };
            for i in (tl0..start).rev() {
                let l: Lit = self.trail[i];
                let vi = l.vi();
                if seen[vi] {
                    if self.vars[vi].reason == NULL_CLAUSE {
                        self.conflicts.push(l.negate());
                    } else {
                        for l in &ch.lits[1..] {
                            let vi = l.vi();
                            if 0 < self.vars[vi].level {
                                seen[vi] = true;
                            }
                        }
                    }
                }
                seen[vi] = false;
            }
        }
    }
}

impl Solver {
    /// renamed from litRedundant
    fn analyze_removable(&mut self, l: Lit, to_clear: &mut Vec<Lit>, level_map: &[bool]) -> bool {
        let Solver { ref mut cp, ref vars, ref mut an_seen, .. } = self;
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
                    if vars[vi].reason != NULL_CLAUSE && level_map[lv as usize]
                    {
                        an_seen[vi] = true;
                        stack.push(*q);
                        to_clear.push(*q);
                    } else {
                        for _ in top..to_clear.len() {
                            an_seen[to_clear.pop().unwrap().vi()] = false;
                        }
                        return false;
                    }
                }
            }
        }
        true
    }

    fn minimize_with_bi_clauses(&mut self, vec: &mut Vec<Lit>) {
        let Solver { ref cp, ref vars, ref mut lbd_temp, .. } = self;
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
        for ci in cp[ClauseKind::Binclause as usize].iter_watcher(l0) {
            let ch = &cp[ClauseKind::Binclause as usize].head[ci];
            debug_assert!(ch.lit[0] == l0 || ch.lit[1] == l0);
            let other = ch.lit[(ch.lit[0] == l0) as usize];
            let vi = other.vi();
            if lbd_temp[vi] == key && self.vars.assigned(other) == LTRUE {
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

    pub fn uncheck_enqueue(&mut self, l: Lit, cid: ClauseId) {
        let Solver {
            ref mut cp,
            ref mut vars,
            ref mut trail,
            ref trail_lim,
            ref mut eliminator,
            .. } = self;
        // println!("uncheck_enqueue {}", l.int());
        debug_assert!(l != 0, "Null literal is about to be equeued");
        debug_assert!(trail_lim.is_empty() || cid != 0,
                      "Null CLAUSE is used for uncheck_enqueue"
        );
        let dl = trail_lim.len();
        let v = &mut vars[l.vi()];
        debug_assert!(!v.eliminated);
        debug_assert!(v.assign == l.lbool() || v.assign == BOTTOM);
        v.assign = l.lbool();
        v.level = dl;
        v.reason = cid;
        if dl == 0 {
            eliminator.enqueue_var(v);
            // self.var_order.remove(&self.vars, l.vi());
        }
        clause_mut!(*cp, cid).set_flag(ClauseFlag::Locked, true);
        // debug_assert!(!self.trail.contains(&l));
        // debug_assert!(!self.trail.contains(&l.negate()));
        trail.push(l);
    }
    pub fn uncheck_assume(&mut self, l: Lit) {
        // println!("uncheck_assume {}", l.int());
        let Solver {
            ref mut vars,
            ref mut trail,
            ref mut trail_lim,
            ref mut eliminator,
            .. } = self;
        trail_lim.push(trail.len());
        let dl = trail_lim.len();
        let v = &mut vars[l.vi()];
        debug_assert!(!v.eliminated);
        debug_assert!(v.assign == l.lbool() || v.assign == BOTTOM);
        v.assign = l.lbool();
        v.level = dl;
        v.reason = NULL_CLAUSE;
        if dl == 0 {
            eliminator.enqueue_var(v);
        }
        // debug_assert!(!trail.contains(&l));
        // debug_assert!(!trail.contains(&l.negate()));
        trail.push(l);
    }
}

impl Solver {
    #[allow(dead_code)]
    fn dump_cnf(&self, fname: &str) {
        let Solver { ref cp, ref vars, ref trail, ref num_vars, .. } = self;
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
            let nv = trail.len();
            let nc: usize = cp.iter().map(|p| p.head.len() - 1).sum();
            buf.write_all(format!("p cnf {} {}\n", num_vars, nc + nv).as_bytes()).unwrap();
            let kinds = [
                ClauseKind::Binclause,
                ClauseKind::Removable,
                ClauseKind::Permanent,
            ];
            for kind in &kinds {
                for c in cp[*kind as usize].head.iter().skip(1) {
                    for l in &c.lits {
                        buf.write_all(format!("{} ", l.int()).as_bytes()).unwrap();
                    }
                    buf.write_all(b"0\n").unwrap();
                }
            }
            buf.write_all(b"c from trail\n").unwrap();
            for x in trail {
                buf.write_all(format!("{} 0\n", x.int()).as_bytes()).unwrap();
            }
        }
    }
    pub fn dump(&self, str: &str) {
        println!("# {} at {}", str, self.decision_level());
        println!(
            "# nassigns {}, decision cands {}",
            self.num_assigns(),
            self.var_order.len()
        );
        let v = self.trail.iter().map(|l| l.int()).collect::<Vec<i32>>();
        let len = self.trail_lim.len();
        if 0 < len {
            print!("# - trail[{}]  [", self.trail.len());
            if 0 < self.trail_lim[0] {
                print!("0{:?}, ", &self.trail[0..self.trail_lim[0]]);
            }
            for i in 0..(len - 1) {
                print!(
                    "{}{:?}, ",
                    i + 1,
                    &v[self.trail_lim[i]..self.trail_lim[i + 1]]
                );
            }
            println!("{}{:?}]", len, &v[self.trail_lim[len - 1]..]);
        } else {
            println!("# - trail[  0]  [0{:?}]", &v);
        }
        println!("- trail_lim  {:?}", self.trail_lim);
        // println!("{}", self.var_order);
        // self.var_order.check("");
    }
}

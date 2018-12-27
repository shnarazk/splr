/// no-watchlist
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
        let _sve = cfg.use_sve;
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
            eliminator: Eliminator::new(false),
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
                            for l in &ch.lits {
                                learnts.touched[l.negate() as usize] = true;
                            }
                            permanents.new_clause(
                                &ch.lits,
                                ch.rank,
                                ch.mass,
                                ch.get_flag(ClauseFlag::Locked),
                            );
                            ch.set_flag(ClauseFlag::Dead, true);
                        }
                    }
                    garbage_collect(&mut self.cp, &mut self.vars, &mut self.eliminator);
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
        self.config.use_sve = false;
        self.eliminator.use_elim = false;
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
        let dl = trail_lim.len();
        let mut in_conflict = NULL_CLAUSE;
        while *q_head < trail.len() {
            let p: Lit = trail[*q_head];
            *q_head += 1;
            stat[Stat::Propagation as usize] += 1;
            unsafe
            {
                let ps = [
                    &vars[p.vi()].neg_occurs as *const Vec<ClauseId>,
                    &vars[p.vi()].pos_occurs as *const Vec<ClauseId>,
                ];
                for list in &ps {
                'next: for cid in &**list {
                    let mut ch = clause_mut!(*cp, cid);
                    if ch.mass <= 0 || ch.get_flag(ClauseFlag::Dead) { continue; }
                    ch.mass -= 1;
                    match ch.mass {
                        _ if in_conflict != NULL_CLAUSE => continue,
                        0 => {
                            for lk in &ch.lits {
                                if vars[lk.vi()].assign == lk.lbool() {
                                    continue 'next;
                                }
                            }
                            in_conflict = *cid;
                            // *q_head = trail.len();
                        }
                        1 => {
                            let mut prop = 0;
                            // print!(" - {:?}: ", vec2int(&ch.lits));
                            for lk in &ch.lits {
                                let v = &vars[lk.vi()];
                                if v.assign == lk.lbool() {
                                    // println!("{}:sat, ", lk.int());
                                    continue 'next;
                                } else if v.assign == BOTTOM && !v.eliminated {
                                    // print!("{}:unbound, ", lk.int());
                                    prop = *lk;
                                    continue;
                                }
                                // print!("{}({}):unsat, ", lk.int(), v.assign);
                            }
                            // println!("");
                            if prop == 0 {
                                // println!("conflict by {:?} for {} at {:?} : {:?}", vec2int(&ch.lits), p.int(), trail_lim.len(), vec2int(trail));
                                in_conflict = *cid;
                            } else {
                                trail.push(prop); // unit propagation
                                // println!("uncheck_enqueue {:?} by {}{:?} @ {}",
                                //          vec2int(&trail),
                                //          cid2fmt(*cid),
                                //          vec2int(&ch.lits),
                                //          dl);
                                let v = &mut vars[prop.vi()];
                                v.assign = prop.lbool();
                                v.level = dl;
                                assert!(v.reason == NULL_CLAUSE);
                                if dl == 0 {
                                    v.reason = NULL_CLAUSE;
                                } else {
                                    v.reason = *cid;
                                    ch.set_flag(ClauseFlag::Locked, true);
                                }
                            }
                        }
                        _ => (),
                    }
                }
                }
            }
        }
        in_conflict
    }

    /// for eliminater invoked by simplify
    fn propagate_0(&mut self) -> ClauseId {
        self.propagate()
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
                    // println!("analyze returned a unit clause {}", l.int());
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
                    // println!("uncheck enqueue {:?} by a new learnt {}{:?}",
                    //          vec2int(&self.trail),
                    //          cid2fmt(cid),
                    //          vec2int(&clause!(self.cp, cid).lits),
                    // );
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
        // println!("cancel_until: trail {:?}", vec2int(trail));
        let lim = trail_lim[lv];
        for l in &trail[lim..] {
            let vi = l.vi();
            let v = &mut vars[vi];
            v.phase = v.assign;
            v.assign = BOTTOM;
            // println!(" - {} {}", l.int(), v.assign);
            if v.reason != NULL_CLAUSE {
                clause_mut!(*cp, v.reason).set_flag(ClauseFlag::Locked, false);
                v.reason = NULL_CLAUSE;
            }
            for cid in &v.pos_occurs {
                clause_mut!(*cp, cid).mass += 1;
            }
            for cid in &v.neg_occurs {
                clause_mut!(*cp, cid).mass += 1;
            }
            var_order.insert(vars, vi);
        }
        trail.truncate(lim);
        trail_lim.truncate(lv);
        // println!("cancel_until: done {:?} to {}", vec2int(trail), trail_lim.len());
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
        // let mut p = (*self.trail.last().unwrap()).negate();
        let mut ti = self.trail.len() - 1; // trail index
        let mut path_cnt = 0;
        // let mut last_dl: Vec<Lit> = Vec::new();
        loop {
            // println!("analyze Lit {}", p.int());
            unsafe {
                debug_assert_ne!(cid, NULL_CLAUSE);
                let ch = clause_mut!(self.cp, cid) as *mut ClauseHead;
                if cid.to_kind() == (ClauseKind::Removable as usize) {
                    // self.bump_cid(cid);
                    self.cp[ClauseKind::Removable as usize].bump_activity(
                        cid.to_index(),
                        self.stat[Stat::Conflict as usize] as f64,
                        &mut self.cla_inc,
                    );
                }
                debug_assert!(!(*ch).get_flag(ClauseFlag::Dead));
                // println!("{}の原因節{}{:?}を逆伝搬", p.int(), cid2fmt(cid), vec2int(&(*ch).lits));
                //for q in &(*ch).lits[((p != NULL_LIT) as usize)..] {
                for q in &(*ch).lits {
                    if *q == p {
                        // println!("{}は出力なので無視", q.int());
                        continue;
                    }
                    let vi = q.vi();
                    let lvl = self.vars[vi].level;
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
                            path_cnt += 1;
                            // println!("{} はレベル{}なのでフラグを立てる。path_cnt = {}", q.int(), lvl, path_cnt);
                            // if self.vars[vi].reason != NULL_CLAUSE
                            //     && self.vars[vi].reason.to_kind() == ClauseKind::Removable as usize
                            // {
                            //     last_dl.push(*q);
                            // }
                        } else {
                            // println!("{} は割当てレベル{} != 決定レベル{}なので採用", q.int(), lvl, dl);
                            learnt.push(*q);
                        }
                    } else {
                        // if lvl == 0 {
                        //     println!("{} は決定レベル{}での割当てなので無視", q.int(), lvl);
                        // } else {
                        //     println!("{} はもうフラグが立っているので無視", q.int());
                        // }
                    }
                }
                // set the index of the next literal to ti
                while !self.an_seen[self.trail[ti].vi()] {
                    // println!("{} はフラグが立ってないので飛ばす", self.trail[ti].int());
                    ti -= 1;
                }
                p = self.trail[ti];
                // println!("次の対象リテラルは{}、残りpath数は{}", p.int(), path_cnt - 1);
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
        // println!("最後に{}を採用して{:?}", p.negate().int(), vec2int(learnt));
        // simplify phase
        let mut to_clear = Vec::new();
        to_clear.push(p.negate());
        let mut level_map = vec![false; self.decision_level()+1];
        for l in &learnt[1..] {
            to_clear.push(*l);
            level_map[self.vars[l.vi()].level] = true;
        }
        learnt.retain(|l| self.vars[l.vi()].reason == NULL_CLAUSE || !self.analyze_removable(*l, &mut to_clear, &level_map));
        // FIXME FOR NWFP
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
            for q in &(*ch).lits {
                if *q == sl { continue; }
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
        let mut my_temp = vec![0; vars.len()];
        if 6 < nblevels {
            return;
        }
        let key = my_temp[0] + 1;
        my_temp[0] = key;
        for l in &mut *my_temp {
            *l = key - 1;
        }
        for l in &vec[..] {
            // assert!(l.vi() != 0);
            my_temp[l.vi() as usize] = key;
        }
        let l0 = vec[0];
        let mut nb = 0;
        let list = if l0.positive() {
            &self.vars[l0.vi()].pos_occurs
        } else {
            &self.vars[l0.vi()].neg_occurs
        };
        for cid in list {
            if cid.to_kind() != ClauseKind::Binclause as usize {
                continue;
            }
            let ch = &cp[ClauseKind::Binclause as usize].head[cid.to_index()];
            assert!(!ch.get_flag(ClauseFlag::Dead));
            // assert!(ch.lits.len() == 2);
            // assert!(ch.lits[0] != l0 && ch.lits[1] != l0);
            let other = ch.lits[(ch.lits[0] == l0) as usize];
            let vi = other.vi();
            if my_temp[vi] == key && vars.assigned(other) == LTRUE {
                nb += 1;
                my_temp[vi] -= 1;
            }
        }
        if 0 < nb {
            my_temp[l0.vi()] = key;
            vec.retain(|l| my_temp[l.vi()] == key);
        }
        my_temp[0] = key;
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
        // println!("----------------- uncheck_assume {:?} to level {} ----------------", vec2int(&trail), dl);
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

pub fn garbage_collect(cp: &mut [ClausePartition], vars: &mut [Var], eliminator: &mut Eliminator) {
    // unlink from occurs
    for v in vars.iter_mut() {
        if !v.eliminated {
            v.pos_occurs.retain(|&cid| !clause!(cp, cid).get_flag(ClauseFlag::Dead));
            v.neg_occurs.retain(|&cid| !clause!(cp, cid).get_flag(ClauseFlag::Dead));
        }
    }
    // gather to some;
    let kinds = [
        ClauseKind::Binclause as usize,
        ClauseKind::Removable as usize,
        ClauseKind::Permanent as usize,
    ];
    for kind in &kinds {
        let mut garbages: Vec<ClauseIndex> = Vec::new();
        for (i, ch) in cp[*kind].head.iter_mut().enumerate() {
            if ch.get_flag(ClauseFlag::Dead) {
                if eliminator.use_elim {
                    for l in &ch.lits {
                        eliminator.enqueue_var(&mut vars[l.vi()]);
                    }
                }
                garbages.push(i.to_index());
                ch.lits.clear();
            }
        }
    }
}


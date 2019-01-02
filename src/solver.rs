use crate::assign::AssignStack;
use crate::clause::{ClauseManagement, GC, *};
use crate::eliminator::{Eliminator, EliminatorIF};
use crate::profiler::*;
use crate::restart::{luby, QueueOperations, RESTART_BLK, RESTART_THR};
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
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

/// For Solver
pub trait CDCL {
    /// returns `true` for SAT, `false` for UNSAT.
    fn search(&mut self) -> bool;
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
    SumLBD,             // the sum of generated learnts' LBD
    NumBin,             // the number of binary clauses
    NumLBD2,            // the number of clauses which LBD is 2
    EndOfStatIndex,     // Don't use this dummy.
}

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
    pub ok: bool,
    pub root_level: usize,
    pub num_vars: usize,
    pub adapt_strategy: bool,
    pub strategy: SearchStrategy,
    pub use_chan_seok: bool,
    /// decay rate for variable activity
    pub variable_decay_rate: f64,
    /// decay rate for clause activity
    pub clause_decay_rate: f64,
    pub cla_inc: f64,
    pub var_inc: f64,
    pub var_decay: f64,
    pub var_decay_max: f64,
    /// dump stats data during solving
    pub dump_solver_stat_mode: i32,
    /// the coefficients for restarts
    pub ema_coeffs: (i32, i32),
    pub restart_thr: f64,
    pub restart_blk: f64,
    /// restart expansion factor
    pub restart_expansion: f64,
    /// static steps between restarts
    pub restart_step: f64,
    pub luby_restart: bool,
    pub luby_restart_num_conflict: f64,
    pub luby_restart_inc: f64,
    pub luby_current_restarts: usize,
    pub luby_restart_factor: f64,
    pub co_lbd_bound: usize,
    pub inc_reduce_db: usize,
    pub first_reduction: usize,
    pub use_sve: bool,
    pub use_tty: bool,
    pub num_solved_vars: usize,
    pub an_seen: Vec<bool>,
    pub lbd_temp: Vec<usize>,
}

impl Default for SolverConfiguration {
    fn default() -> SolverConfiguration {
        SolverConfiguration {
            ok: true,
            root_level: 0,
            num_vars: 0,
            adapt_strategy: true,
            strategy: SearchStrategy::Initial,
            use_chan_seok: false,
            variable_decay_rate: 0.9,
            clause_decay_rate: 0.999,
            cla_inc: 1.0,
            var_inc: 0.9,
            var_decay: VAR_DECAY,
            var_decay_max: MAX_VAR_DECAY,
            dump_solver_stat_mode: 0,
            ema_coeffs: (2 ^ 5, 2 ^ 15),
            restart_thr: RESTART_THR,
            restart_blk: RESTART_BLK,
            restart_expansion: 1.15,
            restart_step: 100.0,
            luby_restart: false,
            luby_restart_num_conflict: 0.0,
            luby_restart_inc: 2.0,
            luby_current_restarts: 0,
            luby_restart_factor: 100.0,
            co_lbd_bound: 4,
            inc_reduce_db: 300,
            first_reduction: 1000,
            use_sve: true,
            use_tty: true,
            num_solved_vars: 0,
            an_seen: Vec::new(),
            lbd_temp: Vec::new(),
        }
    }
}

/// is the collection of all variables.
pub struct Solver {
    /// major sub modules
    pub config: SolverConfiguration, // Configuration
    pub asgs: AssignStack,
    pub cp: [ClausePartition; 4], // Clauses
    pub eliminator: Eliminator,   // Clause/Variable Elimination
    pub stat: Vec<i64>,           // statistics
    pub vars: Vec<Var>,           // Variables
    /// Variable Order
    pub var_order: VarIdHeap,
    /// renamed from `nbclausesbeforereduce`
    pub next_reduction: usize,
    pub next_restart: u64,
    pub cur_restart: usize,
    pub lbd_queue: VecDeque<usize>,
    pub trail_queue: VecDeque<usize>,
    /// Working memory
    pub profile: Profile,
    pub progress_cnt: i64,
    pub model: Vec<Lbool>,
    pub conflicts: Vec<Lit>,
    pub ema_asg: Ema2,
    pub ema_lbd: Ema2,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
}

const LBD_QUEUE_LEN: usize = 50;
const TRAIL_QUEUE_LEN: usize = 5000;

impl Solver {
    pub fn new(cfg: SolverConfiguration, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let path = &cnf.pathname;
        let (_fe, se) = cfg.ema_coeffs;
        let sve = cfg.use_sve;
        Solver {
            config: cfg,
            asgs: AssignStack::new(nv),
            cp: [
                ClausePartition::build(ClauseKind::Liftedlit, nv, 0),
                ClausePartition::build(ClauseKind::Removable, nv, nc),
                ClausePartition::build(ClauseKind::Permanent, nv, 256),
                ClausePartition::build(ClauseKind::Binclause, nv, 256),
            ],
            eliminator: Eliminator::new(sve),
            stat: vec![0; Stat::EndOfStatIndex as usize],
            vars: Var::new_vars(nv),
            var_order: VarIdHeap::new(nv, nv),
            next_reduction: 1000,
            next_restart: 100,
            cur_restart: 1,
            model: vec![BOTTOM; nv + 1],
            conflicts: vec![],
            profile: Profile::new(&path.to_string()),
            lbd_queue: VecDeque::new(),
            trail_queue: VecDeque::new(),
            ema_asg: Ema2::new(3.8, 50_000.0),   // for blocking 4
            ema_lbd: Ema2::new(160.0, 50_000.0), // for forcing 160
            b_lvl: Ema::new(se),
            c_lvl: Ema::new(se),
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
        let fixed = if self.asgs.is_zero() {
            self.asgs.len()
        } else {
            self.asgs.num_at(0)
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

    pub fn adapt_strategy(&mut self) {
        if !self.config.adapt_strategy {
            return;
        }
        let mut re_init = false;
        let decpc =
            self.stat[Stat::Decision as usize] as f64 / self.stat[Stat::Conflict as usize] as f64;
        if decpc <= 1.2 {
            self.config.strategy = SearchStrategy::LowDecisions;
            re_init = true;
        } else if self.stat[Stat::NoDecisionConflict as usize] < 30_000 {
            self.config.strategy = SearchStrategy::LowSuccesive;
        } else if self.stat[Stat::NoDecisionConflict as usize] > 54_400 {
            self.config.strategy = SearchStrategy::HighSuccesive;
        } else if self.stat[Stat::NumLBD2 as usize] - self.stat[Stat::NumBin as usize] > 20_000 {
            self.config.strategy = SearchStrategy::ManyGlues;
        } else {
            self.config.strategy = SearchStrategy::Generic;
            return;
        }
        match self.config.strategy {
            SearchStrategy::LowDecisions => {
                self.config.use_chan_seok = true;
                self.config.co_lbd_bound = 4;
                let _glureduce = true;
                self.config.first_reduction = 2000;
                self.next_reduction = 2000;
                self.cur_restart = ((self.stat[Stat::Conflict as usize] as f64
                    / self.next_reduction as f64)
                    + 1.0) as usize;
                self.config.inc_reduce_db = 0;
            }
            SearchStrategy::LowSuccesive => {
                self.config.luby_restart = true;
                self.config.luby_restart_factor = 100.0;
                self.config.var_decay = 0.999;
                self.config.var_decay_max = 0.999;
            }
            SearchStrategy::HighSuccesive => {
                self.config.use_chan_seok = true;
                let _glureduce = true;
                self.config.co_lbd_bound = 3;
                self.config.first_reduction = 30000;
                self.config.var_decay = 0.99;
                self.config.var_decay_max = 0.99;
                // randomize_on_restarts = 1;
            }
            SearchStrategy::ManyGlues => {
                self.config.var_decay = 0.91;
                self.config.var_decay_max = 0.91;
            }
            _ => (),
        }
        self.ema_asg.reset();
        self.ema_lbd.reset();
        self.lbd_queue.clear();
        self.stat[Stat::SumLBD as usize] = 0;
        self.stat[Stat::Conflict as usize] = 0;
        let [_, ref mut learnts, ref mut permanents, _] = self.cp;
        if self.config.strategy == SearchStrategy::LowDecisions
            || self.config.strategy == SearchStrategy::HighSuccesive
        {
            // TODO incReduceDB = 0;
            // println!("# Adjusting for low decision levels.");
            // move some clauses with good lbd (col_lbd_bound) to Permanent
            for ch in &mut learnts.head[1..] {
                if ch.get_flag(ClauseFlag::Dead) {
                    continue;
                }
                if ch.rank <= self.config.co_lbd_bound || re_init {
                    if ch.rank <= self.config.co_lbd_bound {
                        permanents.new_clause(&ch.lits, ch.rank);
                    }
                    learnts.touched[ch.lit[0].negate() as usize] = true;
                    learnts.touched[ch.lit[1].negate() as usize] = true;
                    ch.flag_on(ClauseFlag::Dead);
                }
            }
            learnts.garbage_collect(&mut self.vars, &mut self.eliminator);
        }
    }
}

impl SatSolver for Solver {
    fn solve(&mut self) -> SolverResult {
        if !self.config.ok {
            return Ok(Certificate::UNSAT(Vec::new()));
        }
        // TODO: deal with assumptions
        // s.root_level = 0;
        self.config.num_solved_vars = self.asgs.len();
        self.progress("");
        // self.eliminator.use_elim = true;
        self.eliminator.var_queue.clear();
        if self.eliminator.use_elim {
            for v in &mut self.vars[1..] {
                if v.neg_occurs.is_empty() && !v.pos_occurs.is_empty() && v.assign == BOTTOM {
                    debug_assert!(!v.eliminated);
                    debug_assert!(!self.asgs.trail.contains(&v.index.lit(LTRUE)));
                    debug_assert!(!self.asgs.trail.contains(&v.index.lit(LFALSE)));
                    v.assign = LTRUE;
                    self.asgs.push(v.index.lit(LTRUE));
                } else if v.pos_occurs.is_empty() && !v.neg_occurs.is_empty() && v.assign == BOTTOM
                {
                    debug_assert!(!v.eliminated);
                    debug_assert!(!self.asgs.trail.contains(&v.index.lit(LTRUE)));
                    debug_assert!(!self.asgs.trail.contains(&v.index.lit(LFALSE)));
                    v.assign = LFALSE;
                    self.asgs.push(v.index.lit(LFALSE));
                } else if v.pos_occurs.len() == 1 || v.neg_occurs.len() == 1 {
                    self.eliminator.enqueue_var(v);
                }
            }
            self.progress("load");
            self.cp.simplify(
                &mut self.asgs,
                &mut self.config,
                &mut self.eliminator,
                &mut self.stat,
                &mut self.vars,
            );
            self.progress("simp");
        } else {
            self.progress("load");
        }
        // self.config.use_sve = false;
        // self.eliminator.use_elim = false;
        self.stat[Stat::Simplification as usize] += 1;
        if self.search() {
            if !self.config.ok {
                self.asgs
                    .cancel_until(&mut self.vars, &mut self.var_order, 0);
                self.progress("error");
                return Err(SolverException::InternalInconsistent);
            }
            self.progress(self.config.strategy.to_str());
            let mut result = Vec::new();
            for vi in 1..=self.config.num_vars {
                match self.vars[vi].assign {
                    LTRUE => result.push(vi as i32),
                    LFALSE => result.push(0 - vi as i32),
                    _ => result.push(0),
                }
            }
            if self.eliminator.use_elim {
                self.eliminator.extend_model(&mut result);
            }
            self.asgs
                .cancel_until(&mut self.vars, &mut self.var_order, 0);
            Ok(Certificate::SAT(result))
        } else {
            self.progress(self.config.strategy.to_str());
            self.asgs
                .cancel_until(&mut self.vars, &mut self.var_order, 0);
            Ok(Certificate::UNSAT(
                self.conflicts.iter().map(|l| l.int()).collect(),
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
        cfg.an_seen = vec![false; nv + 1];
        cfg.lbd_temp = vec![0; nv + 1];
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
                        s.config.ok = false;
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
            ref mut cp,
            ref mut eliminator,
            ref mut vars,
            ref mut asgs,
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
                let dl = asgs.level();
                asgs.enqueue_null(&mut vars[v[0].vi()], v[0].lbool(), dl);
                Some(NULL_CLAUSE)
            }
            _ => {
                let cid = cp[kind as usize].new_clause(&v, 0);
                vars.attach_clause(cid, clause_mut!(*cp, cid), true, eliminator);
                Some(cid)
            }
        }
    }
}

impl CDCL for Solver {
    /// main loop
    fn search(&mut self) -> bool {
        // let Solver {
        //     ref mut asgs,
        //     ref mut config,
        //     ref mut cp,
        //     ref mut eliminator,
        //     ref mut stat,
        //     ref mut vars,
        //     ref mut var_order,
        //     ref mut lbd_queue,
        //     ref mut trail_queue,
        //     ..
        // } = self;
        let mut conflict_c = 0.0; // for Luby restart
        let mut a_decision_was_made = false;
        if self.config.luby_restart {
            self.config.luby_restart_num_conflict = luby(
                self.config.luby_restart_inc,
                self.config.luby_current_restarts,
            ) * self.config.luby_restart_factor;
        }
        loop {
            self.stat[Stat::Propagation as usize] += 1;
            let ci = propagate(&mut self.asgs, &mut self.cp, &mut self.vars, &mut self.stat);
            if ci == NULL_CLAUSE {
                let na = self.asgs.len();
                let ne = self.eliminator.eliminated_vars;
                // println!("na {} + ne {} = {} >= {}", na, ne, na + ne, self.num_vars);
                if self.config.num_vars <= na + ne {
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
                if (self.config.luby_restart && self.config.luby_restart_num_conflict <= conflict_c)
                    || (!self.config.luby_restart
                        && self.lbd_queue.is_full(LBD_QUEUE_LEN)
                        && ((self.stat[Stat::SumLBD as usize] as f64)
                            / (self.stat[Stat::Conflict as usize] as f64)
                            < self.lbd_queue.average() * self.config.restart_thr))
                {
                    self.stat[Stat::Restart as usize] += 1;
                    self.lbd_queue.clear();
                    self.asgs
                        .cancel_until(&mut self.vars, &mut self.var_order, 0);

                    if self.config.luby_restart {
                        conflict_c = 0.0;
                        self.config.luby_current_restarts += 1;
                        self.config.luby_restart_num_conflict = luby(
                            self.config.luby_restart_inc,
                            self.config.luby_current_restarts,
                        ) * self.config.luby_restart_factor;
                        // println!("luby restart {}", self.luby_restart_num_conflict);
                    }
                    // return
                }
                if self.asgs.level() == 0 {
                    self.cp.simplify(
                        &mut self.asgs,
                        &mut self.config,
                        &mut self.eliminator,
                        &mut self.stat,
                        &mut self.vars,
                    );
                    if !self.config.ok {
                        return false;
                    }
                    self.config.num_solved_vars = self.asgs.len();
                    self.var_order.rebuild(&self.vars);
                }
                // self.force_restart();
                if !self.asgs.remains() {
                    // let na = self.num_assigns();
                    // let ne = self.eliminator.eliminated_vars;
                    // // println!("na {} + ne {} = {} , {}", na, ne, na + ne, self.num_vars);
                    // if na + ne >= self.num_vars {
                    //     panic!("na {} + ne {}", na, ne);
                    // }
                    let vi = self.var_order.select_var(&self.vars);
                    debug_assert_ne!(vi, 0);
                    let p = self.vars[vi].phase;
                    self.asgs
                        .uncheck_assume(&mut self.vars, &mut self.eliminator, vi.lit(p));
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
                let dl = self.asgs.level();
                if dl == self.config.root_level {
                    analyze_final(&self.asgs,
                                  &self.cp,
                                  &self.vars,
                                  &mut self.conflicts,
                                  &mut self.config,
                                  ci,
                                  false);
                    return false;
                }
                if self.stat[Stat::Conflict as usize] % 5000 == 0
                    && self.config.var_decay < self.config.var_decay_max
                {
                    self.config.var_decay += 0.01;
                }
                // let real_len = if self.trail_lim.is_empty() {
                //     self.trail.len()
                // } else {
                //     self.trail.len() - self.trail_lim[0]
                // };
                let real_len = self.asgs.len();
                self.trail_queue.enqueue(TRAIL_QUEUE_LEN, real_len);
                // DYNAMIC BLOCKING RESTART
                let count = self.stat[Stat::Conflict as usize] as u64;
                if 100 < count
                    && self.lbd_queue.is_full(LBD_QUEUE_LEN)
                    && self.config.restart_blk * self.trail_queue.average() < (real_len as f64)
                {
                    self.lbd_queue.clear();
                    self.stat[Stat::BlockRestart as usize] += 1;
                }
                let mut new_learnt: Vec<Lit> = Vec::new();
                let bl = analyze(
                    &mut self.asgs,
                    &mut self.config,
                    &mut self.cp,
                    &mut self.stat,
                    &mut self.vars,
                    &mut self.var_order,
                    ci,
                    &mut new_learnt,
                );
                // let nas = self.num_assigns();
                self.asgs.cancel_until(
                    &mut self.vars,
                    &mut self.var_order,
                    max(bl as usize, self.config.root_level),
                );
                if new_learnt.len() == 1 {
                    let l = new_learnt[0];
                    self.asgs.uncheck_enqueue(&mut self.vars, l, NULL_CLAUSE);
                } else {
                    let lbd = self.vars.compute_lbd(&new_learnt, &mut self.config.lbd_temp);
                    let v = &mut new_learnt;
                    let l0 = v[0];
                    let vlen = v.len();
                    debug_assert!(0 < lbd);
                    let cid = self.cp.add_clause(
                        &mut self.config,
                        &mut self.eliminator,
                        &mut self.vars,
                        &mut *v,
                        lbd,
                        self.stat[Stat::Conflict as usize] as f64,
                    );
                    if lbd <= 2 {
                        self.stat[Stat::NumLBD2 as usize] += 1;
                    }
                    if vlen == 2 {
                        self.stat[Stat::NumBin as usize] += 1;
                    }
                    if cid.to_kind() == ClauseKind::Removable as usize {
                        // clause_body_mut!(self.cp, cid).flag_on(ClauseFlag::JustUsed);
                        // debug_assert!(!ch.get_flag(ClauseFlag::Dead));
                        // self.bump_cid(cid);
                        self.cp[ClauseKind::Removable as usize].bump_activity(
                            cid.to_index(),
                            self.stat[Stat::Conflict as usize] as f64,
                            &mut self.config.cla_inc,
                        );
                    }
                    self.asgs.uncheck_enqueue(&mut self.vars, l0, cid);
                    self.lbd_queue.enqueue(LBD_QUEUE_LEN, lbd);
                    self.stat[Stat::SumLBD as usize] += lbd as i64;
                }
                if self.stat[Stat::Conflict as usize] % 10_000 == 0 {
                    self.progress(self.config.strategy.to_str());
                }
                if self.stat[Stat::Conflict as usize] == 100_000 {
                    self.asgs
                        .cancel_until(&mut self.vars, &mut self.var_order, 0);
                    self.cp.simplify(
                        &mut self.asgs,
                        &mut self.config,
                        &mut self.eliminator,
                        &mut self.stat,
                        &mut self.vars,
                    );
                    // self.rebuild_heap();
                    self.adapt_strategy();
                    // } else if 0 < lbd {
                    //     self.block_restart(lbd, dl, bl, nas);
                }

                // self.decay_var_activity();
                // decay clause activity
                self.config.cla_inc /= self.config.clause_decay_rate;
                // glucose reduction
                let conflicts = self.stat[Stat::Conflict as usize] as usize;
                if self.cur_restart * self.next_reduction <= conflicts {
                    self.cur_restart =
                        ((conflicts as f64) / (self.next_reduction as f64)) as usize + 1;
                    self.cp.reduce(
                        &mut self.eliminator,
                        &mut self.stat,
                        &mut self.vars,
                        &mut self.next_reduction,
                        &mut self.config.lbd_temp,
                    );
                    self.next_reduction += self.config.inc_reduce_db;
                }
                // Since the conflict path pushes a new literal to trail,
                // we don't need to pick up a literal here.
            }
        }
    }

}

fn analyze(asgs: &mut AssignStack,
           config: &mut SolverConfiguration,
           cp: &mut [ClausePartition],
           stat: &mut [i64],
           vars: &mut [Var],
           var_order: &mut VarIdHeap,
           confl: ClauseId,
           learnt: &mut Vec<Lit>) -> usize {
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
                    stat[Stat::Conflict as usize] as f64,
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
                //             clause_body_mut!(*cp, confl).rank = 0
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
                vars[vi].bump_activity(stat[Stat::Conflict as usize] as f64);
                var_order.update(vars, vi);
                if !config.an_seen[vi] && 0 < lvl {
                    config.an_seen[vi] = true;
                    if dl <= lvl {
                        // println!("{} はレベル{}なのでフラグを立てる", q.int(), lvl);
                        path_cnt += 1;
                    // if vars[vi].reason != NULL_CLAUSE
                    //     && vars[vi].reason.to_kind() == ClauseKind::Removable as usize
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
            while !config.an_seen[asgs.trail[ti].vi()] {
                // println!("{} はフラグが立ってないので飛ばす", trail[ti].int());
                ti -= 1;
            }
            p = asgs.trail[ti];
            let next_vi = p.vi();
            cid = vars[next_vi].reason;
            // println!("{} にフラグが立っている。そのpath数は{}, \
            //           そのreason{}を探索", next_vi, path_cnt - 1, cid2fmt(cid));
            config.an_seen[next_vi] = false;
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
    let mut level_map = vec![false; asgs.level() + 1];
    for l in &learnt[1..] {
        to_clear.push(*l);
        level_map[vars[l.vi()].level] = true;
    }
    learnt.retain(|l| {
        vars[l.vi()].reason == NULL_CLAUSE
            || !analyze_removable(cp, vars, &mut config.an_seen, *l, &mut to_clear, &level_map)
    });
    if learnt.len() < 30 {
        minimize_with_bi_clauses(cp, vars, &mut config.lbd_temp, learnt);
    }
    // glucose heuristics
    // let lbd = vars.compute_lbd(learnt, lbd_temp);
    // while let Some(l) = last_dl.pop() {
    //     let vi = l.vi();
    //     if clause!(*cp, vars[vi].reason).rank < lbd {
    //         vars[vi].bump_activity(stat[Stat::Conflict as usize] as f64);
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
        config.an_seen[l.vi()] = false;
    }
    level_to_return
}

/// renamed from litRedundant
fn analyze_removable(cp: &mut [ClausePartition],
                     vars: &[Var],
                     an_seen: &mut [bool],
                     l: Lit,
                     to_clear: &mut Vec<Lit>,
                     level_map: &[bool]) -> bool {
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

impl Solver {
    #[allow(dead_code)]
    fn dump_cnf(&self, fname: &str) {
        let Solver {
            ref asgs,
            ref config,
            ref cp,
            ref vars,
            ..
        } = self;
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
            let nc: usize = cp.iter().map(|p| p.head.len() - 1).sum();
            buf.write_all(format!("p cnf {} {}\n", config.num_vars, nc + nv).as_bytes())
                .unwrap();
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
            for x in &asgs.trail {
                buf.write_all(format!("{} 0\n", x.int()).as_bytes())
                    .unwrap();
            }
        }
    }
    pub fn dump(&self, str: &str) {
        println!("# {} at {}", str, self.asgs.level());
        println!(
            "# nassigns {}, decision cands {}",
            self.asgs.len(),
            self.var_order.len()
        );
        let v = self
            .asgs
            .trail
            .iter()
            .map(|l| l.int())
            .collect::<Vec<i32>>();
        let len = self.asgs.level();
        if 0 < len {
            print!("# - trail[{}]  [", self.asgs.len());
            let lv0 = self.asgs.num_at(0);
            if 0 < lv0 {
                print!("0{:?}, ", &self.asgs.trail[0..lv0]);
            }
            for i in 0..(len - 1) {
                let a = self.asgs.num_at(i);
                let b = self.asgs.num_at(i + 1);
                print!("{}{:?}, ", i + 1, &v[a..b]);
            }
            println!("{}{:?}]", len, &v[self.asgs.num_at(len - 1)..]);
        } else {
            println!("# - trail[  0]  [0{:?}]", &v);
        }
        println!("- trail_lim  {:?}", self.asgs.trail_lim);
        // println!("{}", self.var_order);
        // self.var_order.check("");
    }
}

fn propagate(
    asgs: &mut AssignStack,
    cp: &mut [ClausePartition],
    vars: &mut [Var],
    stat: &mut [i64],
) -> ClauseId {
    while asgs.remains() {
        let p: usize = asgs.sweep() as usize;
        let false_lit = (p as Lit).negate();
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
            unsafe {
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
                            asgs.catchup();
                            return kind.id_from(*pre);
                        } else {
                            // self.uncheck_enqueue(other, kind.id_from((*c).index));
                            let dl = asgs.level();
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
                            }
                            debug_assert!(!v.eliminated);
                            // debug_assert!(!trail.contains(&other));
                            // debug_assert!(!trail.contains(&other.negate()));
                            asgs.push(other);
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
pub fn propagate_0(
    cp: &mut [ClausePartition],
    stat: &mut [i64],
    vars: &mut [Var],
    asgs: &mut AssignStack,
) -> ClauseId {
    while asgs.remains() {
        let p: usize = asgs.sweep() as usize;
        let false_lit = (p as Lit).negate();
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
                            asgs.catchup();
                            return kind.id_from(*pre);
                        } else {
                            // self.uncheck_enqueue(other, kind.id_from((*c).index));
                            // debug_assert!(trail_lim.len() == 0);
                            let other = (*ch).lits[0];
                            let v = &mut vars[other.vi()];
                            debug_assert!(v.assign == other.lbool() || v.assign == BOTTOM);
                            v.assign = other.lbool();
                            v.level = 0;
                            debug_assert!(*pre != NULL_CLAUSE);
                            v.reason = NULL_CLAUSE;
                            debug_assert!(!v.eliminated);
                            // debug_assert!(!trail.contains(&other));debug_
                            // debug_assert!(!trail.contains(&other.negate()));
                            asgs.push(other);
                        }
                    }
                    pre = &mut (*ch).next_watcher[my_index];
                }
            }
        }
    }
    NULL_CLAUSE
}

fn analyze_final(asgs: &AssignStack,
                 cp: &[ClausePartition],
                 vars: &[Var],
                 conflicts: &mut Vec<Lit>,
                 config: &mut SolverConfiguration,
                 ci: ClauseId,
                 skip_first: bool) {
    let mut seen = vec![false; config.num_vars + 1];
    conflicts.clear();
    if config.root_level != 0 {
        let ch = clause!(*cp, ci);
        for l in &ch.lits[skip_first as usize..] {
            let vi = l.vi();
            if 0 < vars[vi].level {
                config.an_seen[vi] = true;
            }
        }
        let tl0 = asgs.num_at(0);
        let start = if asgs.level() <= config.root_level {
            asgs.len()
        } else {
            asgs.num_at(config.root_level)
        };
        for i in (tl0..start).rev() {
            let l: Lit = asgs.trail[i];
            let vi = l.vi();
            if seen[vi] {
                if vars[vi].reason == NULL_CLAUSE {
                    conflicts.push(l.negate());
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

fn minimize_with_bi_clauses(cp: &[ClausePartition],
                            vars: &[Var],
                            lbd_temp: &mut [usize],
                            vec: &mut Vec<Lit>) {
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

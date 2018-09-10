use clause::*;
use clause_manage::ClauseManagement;
use solver_propagate::SolveSAT;
use solver_rollback::Restart;
use std::fs;
use std::io::{BufRead, BufReader};
use types::Dump;
use types::*;
use var::*;
// use var_manage::Eliminator;

pub trait SatSolver {
    fn decision_level(&self) -> usize;
    fn solve(&mut self) -> SolverResult;
    fn build(path: &str) -> (Solver, CNFDescription);
    fn add_clause(&mut self, v: Vec<Lit>) -> bool;
    fn add_learnt(&mut self, v: Vec<Lit>) -> usize;
    fn attach_clause(&mut self, c: Clause) -> ClauseId; // only for eliminator
    fn num_assigns(&self) -> usize;
}

/// normal results returned by Solver
#[derive(Debug)]
pub enum Certificate {
    SAT(Vec<i32>),
    UNSAT(Vec<i32>), // FIXME: replace with DRAT
}

/// abnormal termination flags
#[derive(Debug)]
pub enum SolverException {
    StateUNSAT = 0,
    StateSAT,             // 1
    OutOfMemory,          // 2
    TimeOut,              // 3
    InternalInconsistent, // 4
    UndescribedError,     // 5
}

/// The type that `Solver` returns
/// This captures the following three cases:
/// * solved with a satisfiable assingment,
/// * proved that it's an unsatisfiable problem, and
/// * aborted due to Mios specification or an internal error
pub type SolverResult = Result<Certificate, SolverException>;

/// stat index
#[derive(Copy, Clone)]
pub enum Stat {
    NumOfBackjump = 0,   // the number of backjump
    NumOfRestart,        // the number of restart
    NumOfBlockRestart,   // the number of blacking start
    NumOfPropagation,    // the number of propagation
    NumOfReduction,      // the number of reduction
    NumOfSimplification, // the number of simplification
    NumOfClause,         // the number of 'alive' given clauses
    NumOfLearnt,         // the number of 'alive' learnt clauses
    NumOfVariable,       // the number of 'alive' variables
    NumOfGroundVar,      // the number os assined variables at level 0
    NumOfAssign,         // the number of assigned variables
    EndOfStatIndex,      // Don't use this dummy.
}

#[derive(Debug)]
pub struct AssignState {
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
}

/// is the collection of all variables.
#[derive(Debug)]
pub struct Solver {
    /// Configuration
    pub config: SolverConfiguration,
    pub num_vars: usize,
    pub cla_inc: f64,
    pub root_level: usize,
    /// Variable Assignment Management
    pub vars: Vec<Var>,
    pub assign: AssignState,
    /// Variable Order
    pub var_order: VarIdHeap,
    /// Clause Database Management
    pub cp: [ClausePack; 3],
    pub next_reduction: usize,
    pub cur_restart: usize,
    pub num_solved_vars: usize,
    /// Variable Elimination
    pub eliminator: Eliminator,
    /// Working memory
    pub ok: bool,
    pub model: Vec<Lbool>,
    pub conflicts: Vec<Lit>,
    pub stats: Vec<i64>,
    pub an_seen: Vec<Lit>,
    pub an_to_clear: Vec<Lit>,
    pub an_stack: Vec<Lit>,
    pub an_last_dl: Vec<Lit>,
    pub an_learnt_lits: Vec<Lit>,
    pub an_level_map: Vec<usize>,
    pub an_level_map_key: usize,
    pub mi_var_map: Vec<usize>,
    pub lbd_seen: Vec<u64>,
    /// restart heuristics
    pub ema_asg: Ema2,
    pub ema_lbd: Ema2,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub next_restart: u64,
    pub restart_exp: f64,
    pub rbias: Ema,
}

impl Solver {
    pub fn new(cfg: SolverConfiguration, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let assign = AssignState {
            trail: Vec::with_capacity(nv),
            trail_lim: Vec::new(),
            q_head: 0,
        };
        let (_fe, se) = cfg.ema_coeffs;
        let re = cfg.restart_expansion;
        let cdr = cfg.clause_decay_rate;
        let use_sve = cfg.use_sve;
        let s = Solver {
            config: cfg,
            num_vars: nv,
            cla_inc: cdr,
            root_level: 0,
            vars: Var::new_vars(nv),
            assign,
            var_order: VarIdHeap::new(VarOrder::ByActivity, nv, nv),
            cp: [
                ClausePack::build(ClauseKind::Removable, nv, nc),
                ClausePack::build(ClauseKind::Permanent, nv, 256),
                ClausePack::build(ClauseKind::Binclause, nv, 256),
            ],
            next_reduction: 2000,
            cur_restart: 1,
            num_solved_vars: 0,
            eliminator: Eliminator::new(use_sve, nv),
            ok: true,
            model: vec![BOTTOM; nv + 1],
            conflicts: vec![],
            stats: vec![0; Stat::EndOfStatIndex as usize],
            an_seen: vec![0; nv + 1],
            an_to_clear: vec![0; nv + 1],
            an_stack: vec![],
            an_last_dl: vec![],
            an_learnt_lits: vec![],
            an_level_map: vec![0; nv + 1],
            an_level_map_key: 1,
            mi_var_map: vec![0; nv + 1],
            lbd_seen: vec![0; nv + 1],
            //ema_asg: Ema2::new(4000.0, 8192.0), // for blocking
            //ema_lbd: Ema2::new(40.0, 8192.0),   // for forcing
            ema_asg: Ema2::new(30.0, 2000.0), // for blocking
            ema_lbd: Ema2::new(30.0, 2000.0), // for forcing
            b_lvl: Ema::new(se),
            c_lvl: Ema::new(se),
            next_restart: 100,
            restart_exp: re,
            rbias: Ema::new(se),
        };
        s
    }
    // print a progress report
    pub fn progress(&self, mes: &str) -> () {
        let nv = self.vars.len() - 1;
        let k = if self.assign.trail_lim.is_empty() {
            self.assign.trail.len()
        } else {
            self.assign.trail_lim[0]
        };
        let sum = k + self.eliminator.eliminated_vars;
        let deads = self.cp[ClauseKind::Removable as usize]
            .clauses
            .iter()
            .filter(|c| c.dead)
            .count();
        let cnt = self.cp[ClauseKind::Removable as usize]
            .clauses
            .iter()
            .filter(|c| c.rank <= 2)
            .count();
        println!(
            "#{}, DB:R|P|B,{:>7},{:>6},{:>5},{:>7},{:>5}, PROG,{:>5}+{:>5}({:>.3}%),RES:b|f,{:>5},{:>5},EMA:a|l,{:>5.2},{:>6.2},LBD,{:>6.2}",
            mes,
            self.cp[ClauseKind::Removable as usize].clauses.len() - 1,
            cnt,
            deads,
            self.cp[ClauseKind::Permanent as usize].clauses.len() - 1,
            self.cp[ClauseKind::Binclause as usize].clauses.len() - 1,
            k,
            self.eliminator.eliminated_vars,
            (sum as f32) / (nv as f32) * 100.0,
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
            self.ema_asg.get(),
            self.ema_lbd.get(),
            self.ema_lbd.fast,
        );
    }
}

impl SatSolver for Solver {
    fn decision_level(&self) -> usize {
        self.assign.trail_lim.len()
    }
    fn solve(&mut self) -> SolverResult {
        if !self.ok {
            return Ok(Certificate::UNSAT(Vec::new()));
        }
        // TODO deal with assumptions
        self.num_solved_vars = self.assign.trail.len();
        if self.eliminator.use_elim {
            self.eliminate_binclauses();
            self.eliminate();
        }
        self.simplify_database();
        match self.search() {
            _ if self.ok == false => {
                self.cancel_until(0);
                Err(SolverException::InternalInconsistent)
            }
            true => {
                let mut result = Vec::new();
                for vi in 1..self.num_vars + 1 {
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
                    if buf.starts_with("c") {
                        continue;
                    }
                    let mut iter = buf.split_whitespace();
                    let mut v: Vec<Lit> = Vec::new();
                    for s in iter {
                        if let Ok(val) = s.parse::<i32>() {
                            if val == 0 {
                                break;
                            } else {
                                v.push(int2lit(val));
                            }
                        }
                    }
                    if v.len() != 0 && !s.add_clause(v) {
                        s.ok = false;
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(s.vars.len() - 1, cnf.num_of_variables);
        (s, cnf)
    }
    // renamed from clause_new
    fn add_clause(&mut self, mut v: Vec<Lit>) -> bool {
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means totology.
        for i in 0..v.len() {
            let li = v[i];
            let sat = (&self.vars[..]).assigned(li);
            if sat == LTRUE || li.negate() == l_ {
                return true;
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
            0 => false, // Empty clause is UNSAT.
            1 => self.assign.enqueue(&mut self.vars[v[0].vi()], v[0], NULL_CLAUSE),
            _ => {
                self.attach_clause(Clause::new(kind, false, 0, v, false));
                true
            }
        }
    }
    /// renamed from newLearntClause
    fn add_learnt(&mut self, mut v: Vec<Lit>) -> usize {
        if v.len() == 1 {
            self.assign.uncheck_enqueue(&mut self.vars[v[0].vi()], v[0], NULL_CLAUSE);
            0;
        }
        let lbd;
        if v.len() == 2 {
            lbd = 0;
        } else {
            lbd = self.lbd_of(&v);
        }
        let mut i_max = 0;
        let mut lv_max = 0;
        // seek a literal with max level
        for i in 0..v.len() {
            let vi = v[i].vi();
            let lv = self.vars[vi].level;
            if self.vars[vi].assign != BOTTOM && lv_max < lv {
                i_max = i;
                lv_max = lv;
            }
        }
        v.swap(1, i_max);
        let l0 = v[0];
        let kind = if v.len() == 2 {
            ClauseKind::Binclause
        } else {
            ClauseKind::Removable
        };
        let cid = self.attach_clause(Clause::new(kind, true, lbd, v, true));
        self.bump_cid(cid);
        self.assign.uncheck_enqueue(&mut self.vars[l0.vi()], l0, cid);
        lbd
    }
    fn attach_clause(&mut self, c: Clause) -> ClauseId {
        if self.eliminator.use_elim {
            for i in 0..c.len() {
                let l = lindex!(c, i);
                self.vars[l.vi()].touched = true;
                self.eliminator.n_touched += 1;
            }
        }
        let bin = c.kind == ClauseKind::Binclause;
        let cid = self.cp[c.kind as usize].attach(c);
        if self.eliminator.use_elim && bin {
            self.eliminator.binclause_queue.push(cid);
        }
        debug_assert_ne!(cid, 0);
        cid
    }
    fn num_assigns(&self) -> usize {
        self.assign.trail.len()
    }
}

impl Dump for Solver {
    fn dump(&self, str: &str) -> () {
        println!(
            "# {} at {} r:{}, p:{}, b:{}",
            str,
            self.decision_level(),
            self.cp[ClauseKind::Removable as usize].clauses.len(),
            self.cp[ClauseKind::Permanent as usize].clauses.len(),
            self.cp[ClauseKind::Binclause as usize].clauses.len(),
        );
        println!(
            "# nassigns {}, decision cands {}",
            self.num_assigns(),
            self.var_order.len()
        );
        let v = self
            .assign
            .trail
            .iter()
            .map(|l| l.int())
            .collect::<Vec<i32>>();
        let len = self.assign.trail_lim.len();
        if 0 < len {
            print!("# - trail[{}]  [", self.assign.trail.len());
            if 0 < self.assign.trail_lim[0] {
                print!("0{:?}, ", &self.assign.trail[0..self.assign.trail_lim[0]]);
            }
            for i in 0..(len - 1) {
                print!(
                    "{}{:?}, ",
                    i + 1,
                    &v[self.assign.trail_lim[i]..self.assign.trail_lim[i + 1]]
                );
            }
            println!("{}{:?}]", len, &v[self.assign.trail_lim[len - 1]..]);
        } else {
            println!("# - trail[  0]  [0{:?}]", &v);
        }
        println!("- trail_lim  {:?}", self.assign.trail_lim);
        if false {
            // TODO: dump watches links
        }
        if false {
            self.var_order.dump();
            // self.var_order.check("");
        }
    }
}

pub trait Assignment {
    fn enqueue(&mut self, v: &mut Var, l: Lit, cid: ClauseId) -> bool;
    fn uncheck_enqueue(&mut self, v: &mut Var, l: Lit, cid: ClauseId) -> ();
    fn uncheck_assume(&mut self, v: &mut Var, l: Lit) -> ();
}

impl Assignment for AssignState {
    /// This function touches:
    ///  - vars
    ///  - trail
    ///  - trail_lim
    fn uncheck_enqueue(&mut self, v: &mut Var, l: Lit, cid: ClauseId) -> () {
        v.assign = l.lbool();
        v.level = self.trail_lim.len();
        v.reason = cid;
        // mref!(self.cp, cid).locked = true;
        self.trail.push(l);
    }

    fn uncheck_assume(&mut self, v: &mut Var, l: Lit) -> () {
        self.trail_lim.push(self.trail.len());
        self.uncheck_enqueue(v, l, NULL_CLAUSE);
    }
    /// This function touches:
    ///  - vars
    ///  - trail
    fn enqueue(&mut self, v: &mut Var, l: Lit, cid: ClauseId) -> bool {
        // println!("enqueue: {} by {}", l.int(), cid);
        let sig = l.lbool();
        let val = v.assign;
        if val == BOTTOM {
            v.assign = sig;
            v.level = self.trail_lim.len();
            v.reason = cid;
            // mref!(self.cp, cid).locked = true;
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }

}
//impl Solver {
//    pub fn uncheck_enqueue_(&mut self, l: Lit, cid: ClauseId) -> () {
//        debug_assert!(l != 0, "Null literal is about to be equeued");
//        let dl = self.decision_level();
//        let v = &mut self.vars[l.vi()];
//        v.assign = l.lbool();
//        v.level = dl;
//        v.reason = cid;
//        mref!(self.cp, cid).locked = true;
//        self.trail.push(l);
//    }
//}

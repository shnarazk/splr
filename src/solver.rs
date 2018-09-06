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
    fn solve(&mut self) -> SolverResult;
    fn build(path: &str) -> (Solver, CNFDescription);
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
/// * solved with a satisfiable assigment,
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
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
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
            trail: Vec::with_capacity(nv),
            trail_lim: Vec::new(),
            q_head: 0,
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
            ema_asg: Ema2::new(50.0, 1000.0),   // for blocking
            ema_lbd: Ema2::new(50.0, 1000.0),   // for forcing
            b_lvl: Ema::new(se),
            c_lvl: Ema::new(se),
            next_restart: 100,
            restart_exp: re,
            rbias: Ema::new(se),
        };
        s
    }
    #[inline]
    pub fn assigned(&self, l: Lit) -> Lbool {
        self.vars.assigned(l)
    }
    #[inline]
    pub fn satisfies(&self, c: &Clause) -> bool {
        self.vars.satisfies(c)
    }
    pub fn num_assigns(&self) -> usize {
        self.trail.len()
    }
    #[inline]
    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }
    pub fn attach_clause(&mut self, c: Clause) -> ClauseId {
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
}

impl SatSolver for Solver {
    fn solve(&mut self) -> SolverResult {
        if !self.ok {
            return Ok(Certificate::UNSAT(Vec::new()));
        }
        // TODO deal with assumptions
        self.num_solved_vars = self.trail.len();
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
}

impl Dump for Solver {
    fn dump(&self, str: &str) -> () {
        println!("# {} at {} r:{}, p:{}, b:{}", str, self.decision_level(),
                 self.cp[ClauseKind::Removable as usize].clauses.len(),
                 self.cp[ClauseKind::Permanent as usize].clauses.len(),
                 self.cp[ClauseKind::Binclause as usize].clauses.len(),
        );
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
        if false {
            // TODO: dump watches links
        }
        if false {
            self.var_order.dump();
            // self.var_order.check("");
        }
    }
}

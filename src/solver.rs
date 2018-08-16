use clause::*;
use clause_manage::ClauseManagement;
use search::SolveSAT;
use std::collections::HashSet;
use std::fs;
use std::io::{BufRead, BufReader};
use types::*;
use var::*;
use watch::*;

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
    NumOfBackjump = 0, // the number of backjump
    NumOfRestart,      // the number of restart
    NumOfBlockRestart, // the number of blacking start
    NumOfPropagation,  // the number of propagation
    NumOfReduction,    // the number of reduction
    NumOfClause,       // the number of 'alive' given clauses
    NumOfLearnt,       // the number of 'alive' learnt clauses
    NumOfVariable,     // the number of 'alive' variables
    NumOfGroundVar,    // the number os assined variables at level 0
    NumOfAssigned,     // the number of assigned variables
    EndOfStatIndex,    // Don't use this dummy.
}

/// is the collection of all variables.
#[derive(Debug)]
pub struct Solver {
    /// Assignment Management
    pub vars: Vec<Var>,
    pub clauses: Vec<Clause>,
    /// fixed_len = |NULL| + |given|
    pub fixed_len: usize,
    pub watches: WatchMap,
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
    pub conflicts: Vec<Lit>,
    /// Variable Order
    pub var_order: VarIndexHeap,
    /// Configuration
    pub config: SolverConfiguration,
    pub num_vars: usize,
    pub cla_inc: f64,
    pub var_inc: f64,
    pub root_level: usize,
    /// Database Management
    pub clause_permutation: Vec<usize>,
    pub cur_restart: usize,
    pub nb_clauses_before_reduce: usize,
    pub max_learnts: f64,
    pub num_solved_vars: usize,
    /// Working memory
    pub ok: bool,
    pub an_seen: Vec<Lit>,
    pub an_to_clear: Vec<Lit>,
    pub an_stack: Vec<Lit>,
    pub an_last_dl: Vec<Lit>,
    pub an_learnt_lits: Vec<Lit>,
    pub an_level_map: HashSet<usize>,
    pub stats: Vec<i64>,
    pub lbd_seen: Vec<u64>,
    /// restart heuristics
    pub ema_asg: Ema2,
    pub ema_lbd: Ema2,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub next_restart: u64,
    pub check_restart: u64,
    pub restart_exp: f64,
    pub rbias: Ema,
}

pub trait SatSolver {
    fn solve(&mut self) -> SolverResult;
}

trait Dump {
    fn dump(&self, mes: &str) -> ();
}

impl Solver {
    pub fn new(cfg: SolverConfiguration, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let (fe, se) = cfg.ema_coeffs;
        let re = cfg.restart_expansion;
        let cdr = cfg.clause_decay_rate;
        let vdr = cfg.variable_decay_rate;
        let s = Solver {
            vars: Var::new_vars(nv),
            clauses: new_clause_manager(nc),
            fixed_len: 1 + nc,
            watches: new_watch_map(nv * 2),
            trail: Vec::with_capacity(nv),
            trail_lim: Vec::new(),
            q_head: 0,
            conflicts: vec![],
            var_order: VarIndexHeap::new(nv),
            config: cfg,
            num_vars: nv,
            cla_inc: cdr,
            var_inc: vdr,
            root_level: 0,
            clause_permutation: (0..nc * 2).collect(),
            cur_restart: 1,
            nb_clauses_before_reduce: 2000,
            max_learnts: 2000.0,
            num_solved_vars: 0,
            ok: true,
            an_seen: vec![0; nv + 1],
            an_to_clear: vec![0; nv + 1],
            an_stack: vec![],
            an_last_dl: vec![],
            an_learnt_lits: vec![],
            an_level_map: HashSet::with_capacity(256),
            stats: vec![0; Stat::EndOfStatIndex as usize],
            lbd_seen: vec![0; nv + 1],
            ema_asg: Ema2::new(fe, se),
            ema_lbd: Ema2::new(fe, se),
            b_lvl: Ema::new(se),
            c_lvl: Ema::new(se),
            next_restart: 100,
            check_restart: 50,
            restart_exp: re,
            rbias: Ema::new(se),
        };
        s
    }
    pub fn assigned(&self, l: Lit) -> Lbool {
        let x = self.vars[l.vi()].assign;
        if x == BOTTOM {
            BOTTOM
        } else if l.positive() {
            x
        } else {
            negate_bool(x)
        }
    }
    pub fn satisfies(&self, c: &Clause) -> bool {
        for l in &c.lits {
            if self.assigned(*l) == LTRUE {
                return true;
            }
        }
        false
    }
    pub fn attach_clause(&mut self, mut c: Clause) -> ClauseIndex {
        if c.lits.len() == 1 {
            self.enqueue(c.lits[0], NULL_CLAUSE);
            return 0;
        }
        let w0 = c.lits[0];
        let w1 = c.lits[1];
        let ci = self.clauses.len();
        c.index = ci;
        self.clauses.push(c);
        set_watch(&mut self.watches, ci, w0, w1);
        ci
    }
    pub fn num_assigns(&self) -> usize {
        self.trail.len()
    }
    /// the number of given clause
    /// The numeber might change after simplification
    pub fn num_givencs(&self) -> usize {
        self.fixed_len
    }
    pub fn num_learnts(&self) -> usize {
        self.clauses.len() - self.fixed_len - 1 // 1 for NULL_CLAUSE
    }
    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }
    /// builds and returns a configured solver.
    pub fn build(path: &str) -> (Solver, CNFDescription) {
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
                    if v.len() != 0 {
                        s.add_clause(v);
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(s.vars.len() - 1, cnf.num_of_variables);
        s.fixed_len = s.clauses.len();
        (s, cnf)
    }
}

impl SatSolver for Solver {
    fn solve(&mut self) -> SolverResult {
        // TODO deal with assumptons
        // s.root_level = 0;
        self.num_solved_vars = self.trail.len();
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
                        _ => (),
                    }
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
}

impl Dump for Solver {
    fn dump(&self, str: &str) -> () {
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
        if false {
            for (i, m) in self.watches.iter().enumerate() {
                if !m.is_empty() {
                    println!(
                        "# - watches[{:>3}] => {:?}",
                        (i as Lit).int(),
                        m.iter().map(|w| w.by).collect::<Vec<ClauseIndex>>()
                    );
                }
            }
        }
        if false {
            self.var_order.dump();
            // self.var_order.check("");
        }
    }
}

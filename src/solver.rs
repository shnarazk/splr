#![allow(dead_code)]
#![allow(unused_imports)]
use clause::*;
use types::*;

/// In splr, `watchers` is reseted at the beginning of simplify phase.
/// It's just a mutable vector referring immutable Clause.
/// Because, during propagate, all clauses are immutable.
pub struct Watch {
    pub other: Lit,
    pub by: CID,
    pub to: Lit,
}

/// WatcherVec
pub type WatcherVec = Vec<Vec<Watch>>;

pub fn new_watcher_vec(n: usize) -> WatcherVec {
    let mut vec = Vec::new();
    for _i in 0..n {
        vec.push(Vec::new());
    }
    println!("new_watcher_vec: {} => {}", n, vec.len());
    vec
}

pub struct Solver {
    /// Assignment Management
    pub clauses: ClauseManager,
    pub learnts: ClauseManager,
    pub watches: WatcherVec,
    pub assigns: Vec<LBool>,
    pub phases: Vec<i8>,
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
    pub reason: Vec<CID>,
    pub level: Vec<i32>,
    pub conflicts: Vec<Lit>,
    /// Variable Order
    activities: Vec<f64>,
    order: Vec<Var>,
    /// Configuration
    pub config: SolverConfiguration,
    pub num_vars: usize,
    pub root_level: usize,
    /// Database Size Adjustment
    learnt_size_adj: f64,
    learnt_size_cnt: u64,
    max_learnts: f64,
    /// Working memory
    ok: bool,
    an_seen: Vec<Lit>,
    an_to_clear: Vec<Lit>,
    an_stack: Vec<Lit>,
    an_last_dl: Vec<Lit>,
    an_learnt_lits: Vec<Lit>,
    stats: Vec<usize>,
    lbd_seen: Vec<u64>,
    lbd_key: u64,
    /// restart heuristics
    asg_f: Ema_,
    asg_s: Ema,
    b_lvl: Ema,
    c_lvl: Ema,
    lbd_f: Ema_,
    lbd_s: Ema,
    next_restart: u32,
    restart_exp: f64,
    rbias: Ema_,
}

impl Solver {
    pub fn new(cfg: SolverConfiguration, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let (fe, se) = cfg.ema_coeffs;
        let re = cfg.restart_expansion;
        let s = Solver {
            clauses: ClauseManager::new(cnf.num_of_clauses),
            learnts: ClauseManager::new(cnf.num_of_clauses),
            watches: new_watcher_vec(nv * 2),
            assigns: vec![BOTTOM; nv],
            phases: vec![BOTTOM; nv],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            q_head: 0,
            reason: vec![],
            level: vec![-1; nv],
            conflicts: vec![],
            activities: vec![0.0; nv],
            order: vec![],
            config: cfg,
            num_vars: nv,
            root_level: 0,
            learnt_size_adj: 100.0,
            learnt_size_cnt: 100,
            max_learnts: 2000.0,
            ok: true,
            an_seen: vec![],
            an_to_clear: vec![],
            an_stack: vec![],
            an_last_dl: vec![],
            an_learnt_lits: vec![],
            stats: vec![0; 10],
            lbd_seen: vec![0; nv],
            lbd_key: 0,
            asg_f: Ema_::new(fe),
            asg_s: Ema::new(se),
            b_lvl: Ema::new(fe),
            c_lvl: Ema::new(fe),
            lbd_f: Ema_::new(fe),
            lbd_s: Ema::new(se),
            next_restart: 100,
            restart_exp: re,
            rbias: Ema_::new(se),
        };
        s
    }
    pub fn init(&mut self) -> () {
        self.reason = vec![0; 10];
    }
    pub fn value_of(&self, l: Lit) -> LBool {
        let x = self.assigns[lit2var(l) as usize];
        if x == BOTTOM {
            BOTTOM
        } else if positive_lit(l) {
            x
        } else {
            negate_bool(x)
        }
    }
    pub fn satisfies(&self, c: Clause) -> bool {
        for l in c.lits {
            if self.value_of(l) == LTRUE {
                return true;
            }
        }
        return false;
    }
    pub fn inject(&mut self, c: Clause) -> () {
        println!("inject {}", self.watches.len());
        self.watches[1].push(Watch {
            other: 1,
            by: c.cid,
            to: 0,
        });
        self.clauses.push(0, c);
    }
    fn propagate_by_assign(&mut self, _l: Lit, _c: &mut Clause) -> Lit {
        0
    }
    pub fn num_clauses(&self) -> usize {
        self.clauses.vec.len()
    }
    pub fn num_learnts(&self) -> usize {
        self.learnts.vec.len()
    }
}

pub fn cancel_until(_s: &mut Solver, _l: Lit) -> () {}

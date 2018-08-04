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
    pub reasons: Vec<CID>,
    pub levels: Vec<i32>,
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
    stats: Vec<i64>,
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
            reasons: vec![0; 10],
            levels: vec![-1; nv],
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
    pub fn value_of(&self, l: Lit) -> LBool {
        let x = self.assigns[lit2var(l)];
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
    pub fn num_assigns(&self) -> usize {
        self.trail.len()
    }
    pub fn num_clauses(&self) -> usize {
        self.clauses.vec.len()
    }
    pub fn num_learnts(&self) -> usize {
        self.learnts.vec.len()
    }
    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }
    pub fn var2asg(&self, v: Var) -> LBool {
        self.assigns[v]
    }
    pub fn lit2asg(&self, l: Lit) -> LBool {
        let a = self.assigns[lit2var(l)];
        if positive_lit(l) {
            a
        } else {
            negate_bool(a)
        }
    }
    pub fn locked(&self, c: &Clause) -> bool {
        c.cid == self.reasons[lit2var(c.lits[0])]
    }
    pub fn get_stat(&self, i: &StatIndex) -> i64 {
        self.stats[*i as usize]
    }
    pub fn set_asg(&mut self, v: Var, b: LBool) -> () {
        self.assigns[v] = b
    }
    pub fn enqueue(&mut self, l: Lit, cid: usize) -> bool {
        let sig = lit2lbool(l);
        let v = lit2var(l);
        let val = self.var2asg(v);
        if val != BOTTOM {
            val == sig
        } else {
            let i = v;
            self.assigns[i] = sig;
            self.levels[i] = self.decision_level() as i32;
            self.reasons[i] = cid;
            self.trail.push(l);
            true
        }
    }
    pub fn assume(&mut self, l: Lit) -> bool {
        self.trail_lim.push(self.trail.len());
        self.enqueue(l, NULLID)
    }
    pub fn cancel_until(&mut self, lv: usize) -> () {
        let dl = self.decision_level();
        if lv < dl {
            let lim = self.trail_lim[lv + 1];
            let ts = self.trail.len();
            let mut c = ts;
            while lim < c {
                let x = lit2var(self.trail[c]);
                self.phases[x] = self.assigns[x];
                self.assigns[x] = BOTTOM;
                self.reasons[x] = NULLID;
                // self.undoVO(x);
                c -= 1;
            }
            self.trail.truncate(lim);
            self.trail_lim.truncate(lv);
            self.q_head = lim;
        }
    }
}

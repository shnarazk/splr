#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use clause::*;
use types::*;

/// In splr, `watchers` is reseted at the beginning of simplify phase.
/// It's just a mutable vector referring immutable Clause.
/// Because, during propagate, all clauses are immutable.
pub struct Watch {
    pub other: Lit,
    pub by: ClauseIndex,
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

pub struct Var {
    pub assign: LBool,
    pub phase: LBool,
    pub reason: ClauseIndex,
    pub level: usize,
    pub activity: f64,
}

/// heap of VarIndex
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - heap[0] contains the number of alive elements
pub struct VarIndexHeap {
    heap: Vec<VarIndex>, // order : usize -> VarIndex
    idxs: Vec<usize>,    // VarIndex : -> order : usize
}

impl VarIndexHeap {
    fn new(n: usize) -> VarIndexHeap {
        let mut v1 = Vec::new();
        v1.resize(n + 1, 0);
        let mut v2 = Vec::new();
        v2.resize(n + 1, 0);
        for i in 0..n + 1 {
            v1[i] = i;
            v2[i] = i;
        }
        VarIndexHeap { heap: v1, idxs: v2 }
    }
    /// renamed form numElementsInHeap
    fn len(&self) -> usize {
        self.idxs[0]
    }
    /// renamed from inHeap
    fn contains(&self, v: VarIndex) -> bool {
        self.idxs[v] != 0
    }
    fn percolate_up(&mut self, vec: &Vec<Var>, start: usize) -> () {
        let mut q = start;
        let vq = self.heap[q];
        let aq = vec[vq].activity;
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vec[vp].activity;
                if ap < aq {
                    // move down the current parent, and make it empty
                    self.heap[q] = vp;
                    self.idxs[vp] = q;
                    q = p;
                } else {
                    self.heap[q] = vq;
                    self.idxs[vq] = q;
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, vec: &Vec<Var>, start: usize) -> () {
        let n = self.idxs[0];
        let mut i = start;
        let vi = self.heap[i];
        let ai = vec[vi].activity;
        loop {
            let l = 2 * i; // left
            if l <= n {
                let r = l + 1; // right
                let vl = self.heap[l];
                let vr = self.heap[r];
                let al = vec[vl].activity;
                let ar = vec[vr].activity;
                let (c, vc, ac) = if r <= n && al < ar {
                    (r, vr, ar)
                } else {
                    (l, vr, al)
                };
                if ai < ac {
                    self.heap[i] = vc;
                    self.idxs[vc] = i;
                    i = c;
                } else {
                    self.heap[i] = vi;
                    self.idxs[vi] = i;
                    return;
                }
            } else {
                self.heap[i] = vi;
                self.idxs[vi] = i;
                return;
            }
        }
    }
    /// renamed from incrementHeap, updateVO
    pub fn update(&mut self, vec: &Vec<Var>, v: VarIndex) -> () {
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(vec, start)
        }
    }
    /// renamed from undoVO
    pub fn check_insert(&mut self, vec: &Vec<Var>, v: VarIndex) -> () {
        if !self.contains(v) {
            self.insert(vec, v);
        }
    }
    /// renamed from insertHeap
    fn insert(&mut self, vec: &Vec<Var>, v: VarIndex) -> () {
        let n = self.idxs[0] + 1;
        self.heap[n] = v;
        self.idxs[v] = n;
        self.idxs[0] = n;
        self.percolate_up(vec, n);
    }
    /// renamed from getHeapDown
    fn root(&mut self, vec: &Vec<Var>) -> VarIndex {
        let v1 = self.heap[1];
        let vl = self.heap[self.idxs[0]];
        self.heap[1] = vl;
        self.idxs[vl] = 1;
        self.idxs[v1] = 0;
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(vec, 1);
        }
        v1
    }
}

pub struct Solver {
    /// Assignment Management
    pub vars: Vec<Var>,
    pub clauses: ClauseManager,
    pub learnts: ClauseManager,
    pub watches: WatcherVec,
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
    pub lbd_seen: Vec<u64>,
    pub lbd_key: u64,
    /// restart heuristics
    pub asg_f: Ema_,
    pub asg_s: Ema,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub lbd_f: Ema_,
    pub lbd_s: Ema,
    pub next_restart: u64,
    pub restart_exp: f64,
    pub rbias: Ema_,
}

impl Solver {
    pub fn new(cfg: SolverConfiguration, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let (fe, se) = cfg.ema_coeffs;
        let re = cfg.restart_expansion;
        let cdr = cfg.clause_decay_rate;
        let vdr = cfg.variable_decay_rate;
        let s = Solver {
            clauses: new_clause_maanager(),
            learnts: new_clause_maanager(),
            watches: new_watcher_vec(nv * 2),
            vars: vec![],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            q_head: 0,
            conflicts: vec![],
            var_order: VarIndexHeap::new(nv),
            config: cfg,
            num_vars: nv,
            cla_inc: cdr,
            var_inc: vdr,
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
            if self.value_of(*l) == LTRUE {
                return true;
            }
        }
        return false;
    }
    pub fn inject(&mut self, learnt: bool, mut c: Clause) -> ClauseIndex {
        println!("inject {}", c);
        let w0 = c.lits[0];
        let w1 = c.lits[1];
        let ci = if learnt {
            self.learnts.len() as isize
        } else {
            0 - (self.clauses.len() as isize)
        };
        c.index = ci;
        println!("- the clause index is {}.", ci);
        if learnt {
            self.learnts.push(c);
        } else {
            self.clauses.push(c);
        }
        self.watches[w0.negate() as usize].push(Watch {
            other: w1,
            by: ci,
            to: 0,
        });
        self.watches[w1.negate() as usize].push(Watch {
            other: w0,
            by: ci,
            to: 0,
        });
        ci
    }
    fn propagate_by_assign(&mut self, _l: Lit, _c: &mut Clause) -> Lit {
        0
    }
    pub fn num_assigns(&self) -> usize {
        self.trail.len()
    }
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }
    pub fn num_learnts(&self) -> usize {
        self.learnts.len()
    }
    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }
    pub fn var2asg(&self, v: VarIndex) -> LBool {
        self.vars[v].assign
    }
    pub fn lit2asg(&self, l: Lit) -> LBool {
        let a = self.vars[l.vi()].assign;
        if l.positive() {
            a
        } else {
            negate_bool(a)
        }
    }
    pub fn get_stat(&self, i: &StatIndex) -> i64 {
        self.stats[*i as usize]
    }
    pub fn set_asg(&mut self, v: VarIndex, b: LBool) -> () {
        self.vars[v].assign = b
    }
    pub fn enqueue(&mut self, l: Lit, cid: ClauseIndex) -> bool {
        let sig = l.lbool();
        let val = self.vars[l.vi()].assign;
        if val == BOTTOM {
            {
                let dl = self.decision_level();
                let v = &mut self.vars[l.vi()];
                v.assign = sig;
                v.level = dl;
                v.reason = cid;
            }
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }
    pub fn assume(&mut self, l: Lit) -> bool {
        self.trail_lim.push(self.trail.len());
        self.enqueue(l, NULL_CLAUSE)
    }
    pub fn cancel_until(&mut self, lv: usize) -> () {
        let dl = self.decision_level();
        if lv < dl {
            let lim = self.trail_lim[lv + 1];
            let ts = self.trail.len();
            let mut c = ts;
            while lim < c {
                let vi = self.trail[c].vi();
                let vars = &mut self.vars;
                {
                    let v = &mut vars[vi];
                    v.phase = v.assign;
                    v.assign = BOTTOM;
                    v.reason = NULL_CLAUSE;
                }
                self.var_order.check_insert(vars, vi);
                c -= 1;
            }
            self.trail.truncate(lim);
            self.trail_lim.truncate(lv);
            self.q_head = lim;
        }
    }
    /// Heap operations
    fn select_var(&mut self) -> VarIndex {
        loop {
            let n = self.var_order.len();
            if n == 0 {
                return 0;
            }
            let v = self.var_order.root(&self.vars);
            let x = self.vars[v].assign;
            if x == BOTTOM {
                return v;
            }
        }
    }
}

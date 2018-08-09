#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use clause::*;
use types::*;

/// In splr, `watchers` is reseted at the beginning of simplify phase.
/// It's just a mutable vector referring immutable Clause.
/// Because, during propagate, all clauses are immutable.
#[derive(Debug)]
pub struct Watch {
    pub other: Lit,
    pub by: ClauseIndex,
    pub to: Lit,
}

impl Watch {
    pub fn new(o: Lit, b: ClauseIndex) -> Watch {
        Watch {
            other: o,
            by: b,
            to: NULL_LIT,
        }
    }
}

/// WatcherVec
pub type WatcherVec = Vec<Vec<Watch>>;

pub fn new_watcher_vec(nv: usize) -> WatcherVec {
    let mut vec = Vec::new();
    for _i in 0..2 * nv + 1 {
        vec.push(Vec::new());
    }
    vec
}

pub fn register_to_watches(w: &mut WatcherVec, ci: ClauseIndex, w0: Lit, w1: Lit) -> () {
    if ci == NULL_CLAUSE {
        return;
    }
    w[w0.negate() as usize].push(Watch::new(w1, ci));
    w[w1.negate() as usize].push(Watch::new(w0, ci));
}

/// heap of VarIndex
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - idxs[0] contains the number of alive elements
///   `indx` holds positions. So the unused field 0 can hold the last position as a special case.
#[derive(Debug)]
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
        v2[0] = n;
        VarIndexHeap { heap: v1, idxs: v2 }
    }
    /// renamed form numElementsInHeap
    fn len(&self) -> usize {
        self.idxs[0]
    }
    /// renamed from inHeap
    fn contains(&self, v: VarIndex) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn percolate_up(&mut self, vec: &Vec<Var>, start: usize) -> () {
        let mut q = start;
        let vq = self.heap[q];
        if vq == 0 {
            println!("percolate: vq {} q {}, start {}", vq, q, start);
        }
        let aq = vec[vq].activity;
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                assert_ne!(vq, 0);
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vec[vp].activity;
                if ap < aq {
                    // move down the current parent, and make it empty
                    self.heap[q] = vp;
                    assert_ne!(vp, 0);
                    self.idxs[vp] = q;
                    q = p;
                } else {
                    self.heap[q] = vq;
                    assert_ne!(vq, 0);
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
                    (l, vl, al)
                };
                if ai < ac {
                    self.heap[i] = vc;
                    self.idxs[vc] = i;
                    i = c;
                } else {
                    self.heap[i] = vi;
                    assert_ne!(vi, 0);
                    self.idxs[vi] = i;
                    return;
                }
            } else {
                self.heap[i] = vi;
                assert_ne!(vi, 0);
                self.idxs[vi] = i;
                return;
            }
        }
    }
    /// renamed from incrementHeap, updateVO
    pub fn update(&mut self, vec: &Vec<Var>, v: VarIndex) -> () {
        assert_ne!(v, 0);
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(vec, start)
        }
    }
    /// renamed from undoVO
    fn insert(&mut self, vec: &Vec<Var>, vi: VarIndex) -> () {
        // self.check_var_order("check insert 1");
        if !self.contains(vi) {
            // println!("check_insert (unassign) {}", vi);
            let i = self.idxs[vi];
            let n = self.idxs[0] + 1;
            let vn = self.heap[n];
            self.heap.swap(i, n);
            self.idxs.swap(vi, vn);
            self.idxs[0] = n;
            self.percolate_up(vec, n);
        }
        // self.check_var_order("check insert 2");
    }
    /// renamed from insertHeap
    fn push(&mut self, vec: &Vec<Var>, vi: VarIndex) -> () {
        let n = self.idxs[0] + 1;
        self.heap[n] = vi;
        self.idxs[vi] = n;
        assert_ne!(n, 0);
        self.idxs[0] = n;
        assert_ne!(n, 0);
        self.percolate_up(vec, n);
    }
    /// renamed from getHeapDown
    fn root(&mut self, vec: &Vec<Var>) -> VarIndex {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n];
        // self.check_var_order(&format!("root 1 :[({}, {}) ({}, {})]", s, vs, n, vn));
        assert_ne!(vn, 0);
        assert_ne!(vs, 0);
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(vec, 1);
        }
        // self.check_var_order("root 2");
        vs
    }
    pub fn check(&self, s: &str) -> () {
        let h = &mut self.heap.clone()[1..];
        let d = &mut self.idxs.clone()[1..];
        h.sort();
        d.sort();
        for i in 0..h.len() {
            if h[i] != i + 1 {
                panic!("heap {} {} {:?}", i, h[i], h);
            }
            if d[i] != i + 1 {
                panic!("idxs {} {} {:?}", i, d[i], d);
            }
        }
        println!(" - pass var_order test at {}", s);
    }
}

#[derive(Debug)]
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
    /// Database Management
    pub clause_permutation: Vec<ClauseIndex>,
    pub learnt_permutation: Vec<ClauseIndex>,
    pub learnt_size_adj: f64,
    pub learnt_size_cnt: u64,
    pub max_learnts: f64,
    /// Working memory
    pub ok: Lbool,
    pub an_seen: Vec<Lit>,
    pub an_to_clear: Vec<Lit>,
    pub an_stack: Vec<Lit>,
    pub an_last_dl: Vec<Lit>,
    pub an_learnt_lits: Vec<Lit>,
    pub stats: Vec<i64>,
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
        let nc = cnf.num_of_clauses as usize;
        let (fe, se) = cfg.ema_coeffs;
        let re = cfg.restart_expansion;
        let cdr = cfg.clause_decay_rate;
        let vdr = cfg.variable_decay_rate;
        let s = Solver {
            vars: Var::new_vars(nv),
            clauses: new_clause_manager(),
            learnts: new_clause_manager(),
            watches: new_watcher_vec(nv * 2),
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
            clause_permutation: (0..nc)
                .map(|x| x as ClauseIndex)
                .collect::<Vec<ClauseIndex>>(),
            learnt_permutation: Vec::new(),
            learnt_size_adj: 100.0,
            learnt_size_cnt: 100,
            max_learnts: 2000.0,
            ok: LTRUE,
            an_seen: vec![0; nv + 1],
            an_to_clear: vec![0; nv + 1],
            an_stack: vec![],
            an_last_dl: vec![],
            an_learnt_lits: vec![],
            stats: vec![0; StatIndex::EndOfStatIndex as usize],
            lbd_seen: vec![0; nv + 1],
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
    pub fn iref_clause(&self, ci: ClauseIndex) -> &Clause {
        if 0 < ci {
            &self.learnts[ci as usize]
        } else {
            &self.clauses[(-ci) as usize]
        }
    }
    pub fn mref_clause(&mut self, ci: ClauseIndex) -> &mut Clause {
        if 0 < ci {
            &mut self.learnts[ci as usize]
        } else {
            &mut self.clauses[(-ci) as usize]
        }
    }
    pub fn satisfies(&self, c: &Clause) -> bool {
        for l in &c.lits {
            if self.assigned(*l) == LTRUE {
                return true;
            }
        }
        return false;
    }
    pub fn inject(&mut self, learnt: bool, mut c: Clause) -> ClauseIndex {
        if c.lits.len() == 1 {
            self.enqueue(c.lits[0], NULL_CLAUSE);
            return 0;
        }
        let w0 = c.lits[0];
        let w1 = c.lits[1];
        let ci = if learnt {
            self.learnts.len() as i64
        } else {
            0 - (self.clauses.len() as i64)
        };
        c.index = ci;
        // println!("Inject {}-th clause {}.", ci, c);
        if learnt {
            self.learnts.push(c);
        } else {
            self.clauses.push(c);
        }
        register_to_watches(&mut self.watches, ci, w0, w1);
        ci
    }
    pub fn num_assigns(&self) -> usize {
        self.trail.len()
    }
    pub fn num_clauses(&self) -> usize {
        self.clauses.len() - 1 // 0 is NULL_CLAUSE
    }
    pub fn num_learnts(&self) -> usize {
        self.learnts.len() - 1 // 0 is NULL_CLAUSE
    }
    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }
    pub fn enqueue(&mut self, l: Lit, cid: ClauseIndex) -> bool {
        // println!("enqueue: {} by {}", l.int(), cid);
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
    fn assume(&mut self, l: Lit) -> bool {
        self.trail_lim.push(self.trail.len());
        self.enqueue(l, NULL_CLAUSE)
    }
    pub fn cancel_until(&mut self, lv: usize) -> () {
        if self.decision_level() <= lv {
            return;
        }
        let lim = self.trail_lim[lv];
        for l in &self.trail[lim..] {
            let vi = l.vi();
            // println!("cancell assign {}", vi);
            {
                let v = &mut self.vars[vi];
                v.phase = v.assign;
                v.assign = BOTTOM;
                v.reason = NULL_CLAUSE;
                // println!("rollback vi:{}", vi);
            }
            assert_eq!(self.vars[vi].assign, BOTTOM);
            self.var_order.insert(&self.vars, vi);
        }
        self.trail.truncate(lim); // FIXME
        self.trail_lim.truncate(lv);
        self.q_head = lim;
        // self.dump("cancel_until");
    }
    /// Heap operations; renamed from selectVO
    pub fn select_var(&mut self) -> VarIndex {
        loop {
            // self.check_var_order("select_var 1");
            if self.var_order.idxs[0] == 0 {
                // println!("> select_var returns 0");
                return 0;
            }
            let vi = self.var_order.root(&self.vars);
            // self.check_var_order("select_var 2");
            let x = self.vars[vi].assign;
            if x == BOTTOM {
                return vi;
            }
        }
    }
    pub fn dump(&self, str: &str) -> () {
        println!("# {} at {}", str, self.decision_level());
        println!(
            "# nassigns {}, decision cands {}",
            self.num_assigns(),
            self.var_order.idxs[0]
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
            println!("# - heap {:?}", self.var_order.heap);
            println!("# - idxs {:?}", self.var_order.idxs);
            self.var_order.check("");
        }
    }
}

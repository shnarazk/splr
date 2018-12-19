// use clause::Clause;
use crate::clause::{ClauseFlag, ClauseHead};
use crate::eliminator::{Eliminator, EliminatorIF};
use crate::solver::Solver;
use crate::types::*;
use std::fmt;

/// For Solver
pub trait VarManagement {
    fn select_var(&mut self) -> VarId;
    // fn decay_var_activity(&mut self) -> ();
    fn rebuild_heap(&mut self) -> ();
}

/// For [Var]
pub trait Satisfiability {
    fn assigned(&self, l: Lit) -> Lbool;
    fn satisfies(&self, c: &[Lit]) -> bool;
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize;
}

/// For Vec<Var>
pub trait EliminationIF {
    fn attach_clause(&mut self, cid: ClauseId, ch: &mut ClauseHead, ignorable: bool, eliminator: &mut Eliminator) -> ();
    fn detach_clause(&mut self, cid: ClauseId, ch: &ClauseHead, eliminator: &mut Eliminator) -> ();
}

/// For VarIdHeap
pub trait VarOrdering {
    fn get_root(&mut self, vars: &[Var]) -> VarId;
    fn reset(&mut self) -> ();
    fn contains(&self, v: VarId) -> bool;
    fn update(&mut self, vec: &[Var], v: VarId) -> ();
    fn insert(&mut self, vec: &[Var], v: VarId) -> ();
    fn clear(&mut self) -> ();
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

pub const VAR_DECAY: f64 = 0.9;
pub const MAX_VAR_DECAY: f64 = 0.95;
// const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;

/// Struct for a variable.
pub struct Var {
    pub index: usize,
    pub assign: Lbool,
    pub phase: Lbool,
    pub reason: ClauseId,
    pub level: usize,
    pub activity: f64,
    /// For elimination
    pub touched: bool,
    /// For elimination
    pub eliminated: bool,
    pub pos_occurs: Vec<ClauseId>,
    pub neg_occurs: Vec<ClauseId>,
    pub enqueued: bool,
}

/// is the dummy var index.
pub const NULL_VAR: VarId = 0;

impl Var {
    pub fn new(i: usize) -> Var {
        Var {
            index: i,
            assign: BOTTOM,
            phase: BOTTOM,
            reason: NULL_CLAUSE,
            level: 0,
            activity: 0.0,
            touched: false,
            eliminated: false,
            pos_occurs: Vec::new(),
            neg_occurs: Vec::new(),
            enqueued: false,
        }
    }
    pub fn new_vars(n: usize) -> Vec<Var> {
        let mut vec = Vec::with_capacity(n + 1);
        for i in 0..=n {
            let mut v = Var::new(i);
            v.activity = (n - i) as f64;
            vec.push(v);
        }
        vec
    }
    pub fn bump_activity(&mut self, d: f64) -> () {
        self.activity = (self.activity + d) / 2.0;
        // let a = d + 0.01;
        // self.vars[vi].activity = a;
        // if 1.0e60 < a {
        //     for v in &mut self.vars[1..] {
        //         v.activity *= 1.0e-60;
        //     }
        // }
    }
}

impl Satisfiability for [Var] {
    fn assigned(&self, l: Lit) -> Lbool {
        self[l.vi()].assign ^ ((l & 1) as u8)
    }
    fn satisfies(&self, vec: &[Lit]) -> bool {
        for l in vec {
            if self.assigned(*l) == LTRUE {
                return true;
            }
        }
        false
    }
    /// CAVEAT: call reset_lbd_counter before it
    #[inline(always)]
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize {
        let key = keys[0] + 1;
        keys[0] = key;
        let mut cnt = 0;
        for l in vec {
            let lv = self[l.vi()].level;
            if keys[lv] != key {
                keys[lv] = key;
                cnt += 1;
            }
        }
        cnt
    }
}

impl EliminationIF for Vec<Var> {
    fn attach_clause(&mut self, cid: ClauseId, ch: &mut ClauseHead, ignorable: bool, eliminator: &mut Eliminator) -> () {
        if !eliminator.use_elim {
            return;
        }
        for l in &ch.lits {
            let mut v = &mut self[l.vi()];
            v.touched = true;
            eliminator.n_touched += 1;
            if !v.eliminated {
                if l.positive() {
                    v.pos_occurs.push(cid);
                } else {
                    v.neg_occurs.push(cid);
                }
            }
        }
        if !ignorable {
            eliminator.enqueue_clause(cid, ch);
        }
    }
    fn detach_clause(&mut self, cid: ClauseId, ch: &ClauseHead, eliminator: &mut Eliminator) -> () {
        debug_assert!(ch.get_flag(ClauseFlag::Dead));
        if eliminator.use_elim {
            for l in &ch.lits {
                let v = &mut self[l.vi()];
                if !v.eliminated {
                    // let xx = v.pos_occurs.len() + v.neg_occurs.len();
                    if l.positive() {
                        v.pos_occurs.retain(|&cj| cid != cj);
                    } else {
                        v.neg_occurs.retain(|&cj| cid != cj);
                    }
                    // let xy = v.pos_occurs.len() + v.neg_occurs.len();
                    eliminator.enqueue_var(v);
                }
            }
        }
    }
}

// pub struct VarManager {
//     vec: Vec<Var>,
//     activity_heap: VarIdHeap,
//     eliminator: Eliminator,
// }

pub enum VarOrder {
    ByActivity,
    ByOccurence,
}

/// heap of VarId
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - idxs[0] contains the number of alive elements
///   `indx` holds positions. So the unused field 0 can hold the last position as a special case.
pub struct VarIdHeap {
    // order: VarOrder,
    pub heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>,     // VarId : -> order : usize
}

impl VarOrdering for VarIdHeap {
    /// renamed from getHeapDown
    fn get_root(&mut self, vars: &[Var]) -> VarId {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n];
        // self.var_order.check(&format!("root 1 :[({}, {}) ({}, {})]", s, vs, n, vn));
        // println!("n {} vn {}", n, vn);
        // if vn == 0 {
        //     println!("n {} vn {}", n, vn);
        // }
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vars, 1);
        }
        // self.var_order.check("root 2");
        // chect the validness of the selected var
        // let mut cnt = 0;
        // let mut best = vs;
        // for v in &vars[1..] {
        //     if v.assign == BOTTOM && vars[best].activity < v.activity {
        //         best = v.index;
        //         cnt += 1;
        //     }
        // }
        // if best != vs {
        //     println!("best {}@{}/{} root {} ({})", best, self.idxs[best], self.idxs[0], vs, cnt);
        // }
        vs
    }
    fn reset(&mut self) -> () {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    /// renamed from inHeap
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    /// renamed from incrementHeap, updateVO
    fn update(&mut self, vec: &[Var], v: VarId) -> () {
        debug_assert!(v != 0, "Invalid VarId");
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(vec, start)
        }
    }
    /// renamed from undoVO
    fn insert(&mut self, vec: &[Var], vi: VarId) -> () {
        // self.var_order.check("check insert 1");
        if self.contains(vi) {
            let i = self.idxs[vi];
            self.percolate_up(&vec, i);
            return;
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n];
        self.heap.swap(i, n);
        self.idxs.swap(vi, vn);
        self.idxs[0] = n;
        self.percolate_up(&vec, n);
        // self.var_order.check("check insert 2");
    }
    fn clear(&mut self) -> () {
        self.reset()
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
}

impl VarIdHeap {
    pub fn new(n: usize, init: usize) -> VarIdHeap {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(n);
        for i in 1..=n {
            heap.push(i);
            idxs.push(i);
        }
        idxs[0] = init;
        VarIdHeap { heap, idxs }
    }
    fn percolate_up(&mut self, vars: &[Var], start: usize) -> () {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = vars[vq].activity;
        // let aq = match self.order {
        //     VarOrder::ByActivity => vars[vq].activity,
        //     VarOrder::ByOccurence => vars[vq].occurs.len() as f64,
        // };
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vars[vp].activity;
                // let ap = match self.order {
                //     VarOrder::ByActivity => vars[vp].activity,
                //     VarOrder::ByOccurence => vars[vp].occurs.len() as f64,
                // };
                if ap < aq {
                    // move down the current parent, and make it empty
                    self.heap[q] = vp;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vp] = q;
                    q = p;
                } else {
                    self.heap[q] = vq;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vq] = q;
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, vars: &[Var], start: usize) -> () {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i];
        let ai = vars[vi].activity;
        loop {
            let l = 2 * i; // left
            if l < n {
                let vl = self.heap[l];
                let al = vars[vl].activity;
                // let al = match self.order {
                //     VarOrder::ByActivity => vars[vl].activity,
                //     VarOrder::ByOccurence => vars[vl].occurs.len() as f64,
                // };
                let r = l + 1; // right
                               // let ar = match self.order {
                               //     VarOrder::ByActivity => vars[vr].activity,
                               //     VarOrder::ByOccurence => vars[vr].occurs.len() as f64,
                               // };
                let (target, vc, ac) = if r < n && al < vars[self.heap[r]].activity {
                    let vr = self.heap[r];
                    (r, vr, vars[vr].activity)
                } else {
                    (l, vl, al)
                };
                if ai < ac {
                    self.heap[i] = vc;
                    self.idxs[vc] = i;
                    i = target;
                } else {
                    self.heap[i] = vi;
                    debug_assert!(vi != 0, "invalid index");
                    self.idxs[vi] = i;
                    return;
                }
            } else {
                self.heap[i] = vi;
                debug_assert!(vi != 0, "invalid index");
                self.idxs[vi] = i;
                return;
            }
        }
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
    /// renamed from getHeapDown
    #[allow(dead_code)]
    pub fn remove(&mut self, vec: &[Var], vs: VarId) -> () {
        let s = self.idxs[vs];
        let n = self.idxs[0];
        if n < s {
            return;
        }
        let vn = self.heap[n];
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vec, 1);
        }
    }
    #[allow(dead_code)]
    fn peek(&self) -> VarId {
        self.heap[1]
    }
}

impl VarManagement for Solver {
    fn rebuild_heap(&mut self) -> () {
        debug_assert_eq!(self.decision_level(), 0);
        self.var_order.reset();
        for v in &self.vars[1..] {
            if v.assign == BOTTOM && !v.eliminated {
                self.var_order.insert(&self.vars, v.index);
            }
        }
    }
    // fn decay_var_activity(&mut self) -> () {
    //     // self.var_inc /= self.var_decay;
    // }
    /// Heap operations; renamed from selectVO
    fn select_var(&mut self) -> VarId {
        loop {
            let vi = self.var_order.get_root(&self.vars);
            if self.vars[vi].assign == BOTTOM && !self.vars[vi].eliminated {
                // if self.trail.contains(&vi.lit(LTRUE)) || self.trail.contains(&vi.lit(LFALSE)) {
                //     panic!("@ level {}, select_var vi {} v {:?}", self.trail_lim.len(), vi, self.vars[vi]);
                // }
                return vi;
            }
        }
    }
}

impl fmt::Display for VarIdHeap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            " - seek pointer - nth -> var: {:?}\n - var -> nth: {:?}",
            self.heap, self.idxs,
        )
    }
}

use clause::Clause;
use solver::{Solver, Stat};
use std::fmt;
use types::*;

// for Solver
pub trait VarManagement {
    fn select_var(&mut self) -> VarId;
    fn bump_vi(&mut self, vi: VarId) -> ();
    fn decay_var_activity(&mut self) -> ();
    fn rebuild_vh(&mut self) -> ();
}

/// for [Var]
pub trait Satisfiability {
    fn assigned(&self, l: Lit) -> Lbool;
    fn satisfies(&self, c: &Clause) -> bool;
}

/// for VarIdHeap
pub trait VarOrdering {
    fn get_root(&mut self, vars: &[Var]) -> VarId;
    fn reset(&mut self) -> ();
    fn contains(&self, v: VarId) -> bool;
    fn update(&mut self, vec: &[Var], v: VarId) -> ();
    fn insert(&mut self, vec: &[Var], v: VarId) -> ();
    fn seek_top(&mut self, vars: &[Var]) -> VarId;
    fn update_seek(&mut self, vi: VarId) -> ();
    fn clear(&mut self) -> ();
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

pub const VAR_DECAY: f64 = 0.8;
pub const MAX_VAR_DECAY: f64 = 0.95;
const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;

/// Struct for a variable.
#[derive(Debug)]
pub struct Var {
    pub index: usize,
    pub assign: Lbool,
    pub phase: Lbool,
    pub reason: ClauseId,
    pub level: usize,
    pub activity: f64,
    /// for elimination
    pub frozen: bool,
    /// for elimination
    pub touched: bool,
    /// for elimination
    pub eliminated: bool,
    // for elimination
    pub terminal: bool,
    // for elimination
    pub occurs: Vec<ClauseId>,
    // for elimination
    pub max_clause_size: usize,
    pub num_occurs: usize,
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
            frozen: false,
            touched: false,
            eliminated: false,
            terminal: false,
            occurs: Vec::new(),
            max_clause_size: 0,
            num_occurs: 0,
        }
    }
    pub fn new_vars(n: usize) -> Vec<Var> {
        let mut vec = Vec::with_capacity(n + 1);
        for i in 0..n + 1 {
            let mut v = Var::new(i);
            v.activity = (n - i) as f64;
            vec.push(v);
        }
        vec
    }
}

impl Satisfiability for [Var] {
    #[inline]
    fn assigned(&self, l: Lit) -> Lbool {
        self[l.vi()].assign ^ ((l & 1) as u8)
    }
    fn satisfies(&self, c: &Clause) -> bool {
        for i in 0..c.len() {
            let l = lindex!(c, i);
            if self.assigned(l) == LTRUE {
                return true;
            }
        }
        false
    }
}

// pub struct VarManager {
//     vec: Vec<Var>,
//     activity_heap: VarIdHeap,
//     eliminator: Eliminator,
// }

#[derive(Debug)]
pub enum VarOrder {
    ByActivity,
    ByOccurence,
}

/// heap of VarId
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - idxs[0] contains the number of alive elements
///   `indx` holds positions. So the unused field 0 can hold the last position as a special case.
#[derive(Debug)]
pub struct VarIdHeap {
    order: VarOrder,
    pub heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>,     // VarId : -> order : usize
    seek: usize,
}

impl VarOrdering for VarIdHeap {
    fn get_root(&mut self, vars: &[Var]) -> VarId {
        self.root(vars)
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
    fn seek_top(&mut self, vars: &[Var]) -> VarId {
        loop {
            if self.heap.len() <= self.seek {
                return 0;
            }
            let v = self.heap[self.seek];
            self.seek += 1;
            if vars[v as usize].assign == BOTTOM {
                return v;
            }
        }
    }
    fn update_seek(&mut self, vi: VarId) -> () {
        let n = self.idxs[vi];
        if n < self.seek {
            self.seek = n;
        }
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
    pub fn new(order: VarOrder, n: usize, init: usize) -> VarIdHeap {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(n);
        for i in 1..n + 1 {
            heap.push(i);
            idxs.push(i);
        }
        idxs[0] = init;
        VarIdHeap { order, heap, idxs, seek: 1 }
    }
    /// renamed from getHeapDown
    fn root(&mut self, vec: &[Var]) -> VarId {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n];
        // self.var_order.check(&format!("root 1 :[({}, {}) ({}, {})]", s, vs, n, vn));
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vec, 1);
        }
        // self.var_order.check("root 2");
        vs
    }
    fn percolate_up(&mut self, vec: &[Var], start: usize) -> () {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = vec[vq].activity;
        // let aq = match self.order {
        //     VarOrder::ByActivity => vec[vq].activity,
        //     VarOrder::ByOccurence => vec[vq].occurs.len() as f64,
        // };
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                self.seek = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vec[vp].activity;
                // let ap = match self.order {
                //     VarOrder::ByActivity => vec[vp].activity,
                //     VarOrder::ByOccurence => vec[vp].occurs.len() as f64,
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
                    if q < self.seek {
                        self.seek = q;
                    }
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, vec: &[Var], start: usize) -> () {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i];
        let ai = match self.order {
            VarOrder::ByActivity => vec[vi].activity,
            VarOrder::ByOccurence => vec[vi].occurs.len() as f64,
        };
        loop {
            let l = 2 * i; // left
            if l <= n {
                let r = l + 1; // right
                let vl = self.heap[l];
                let vr = self.heap[r];
                let al = vec[vl].activity;
                // let al = match self.order {
                //     VarOrder::ByActivity => vec[vl].activity,
                //     VarOrder::ByOccurence => vec[vl].occurs.len() as f64,
                // };
                let ar = vec[vr].activity;
                // let ar = match self.order {
                //     VarOrder::ByActivity => vec[vr].activity,
                //     VarOrder::ByOccurence => vec[vr].occurs.len() as f64,
                // };
                let (target, vc, ac) = if r <= n && al < ar {
                    (r, vr, ar)
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
    fn remove(&mut self, vec: &[Var], vs: VarId) -> () {
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
    fn rebuild_vh(&mut self) -> () {
        if self.decision_level() != 0 {
            return;
        }
        self.var_order.reset();
        for vi in 1..self.vars.len() {
            if self.vars[vi].assign == BOTTOM {
                self.var_order.insert(&self.vars, vi);
            }
        }
    }
    fn bump_vi(&mut self, vi: VarId) -> () {
        let d = self.stats[Stat::Conflict as usize] as f64;
        let a = (self.vars[vi].activity + d) / 2.0;
        self.vars[vi].activity = a;
        if VAR_ACTIVITY_THRESHOLD < a {
            // self.rescale_var_activity();
            for i in 1..self.vars.len() {
                self.vars[i].activity /= VAR_ACTIVITY_THRESHOLD;
            }
            self.var_inc /= VAR_ACTIVITY_THRESHOLD;
        }
        self.var_order.update(&self.vars, vi);
    }
    fn decay_var_activity(&mut self) -> () {
        self.var_inc /= self.var_decay;
    }
    /// Heap operations; renamed from selectVO
    fn select_var(&mut self) -> VarId {
        // self.var_order.seek_top(&self.vars)
        loop {
            if self.var_order.len() == 0 {
                return 0;
            }
            let vi = self.var_order.get_root(&self.vars);
            let x = self.vars[vi].assign;
            if x == BOTTOM {
                return vi;
            }
        }
    }
}

impl fmt::Display for VarIdHeap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            " - seek pointer {}\n - clause_queue {:?}\n - heap {:?}",
            self.seek,
            self.heap,
            self.idxs,
        )
    }
}

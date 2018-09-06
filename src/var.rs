#![allow(unused_imports)]
use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::DEAD_CLAUSE;
use types::*;

const BWDSUB_CLAUSE: ClauseId = DEAD_CLAUSE - 1;
const SUBSUMPTION_SIZE: usize = 20;
/// is the dummy var index.
pub const NULL_VAR: VarId = 0;

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
    pub touched: bool,
    /// for elimination
    pub eliminated: bool,
    /// for elimination
    pub elimination_target: bool,
    /// for elimination
    pub pos_occurs: Vec<ClauseId>,
    /// for elimination
    pub neg_occurs: Vec<ClauseId>,
    /// for elimination
    pub bin_pos_occurs: Vec<ClauseId>,
    /// for elimination
    pub bin_neg_occurs: Vec<ClauseId>,
}

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
            elimination_target: false,
            pos_occurs: Vec::new(),
            neg_occurs: Vec::new(),
            bin_pos_occurs: Vec::new(),
            bin_neg_occurs: Vec::new(),
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

pub trait Satisfiability {
    fn assigned(&self, l: Lit) -> Lbool;
    fn satisfies(&self, c: &Clause) -> bool;
}

impl Satisfiability for Vec<Var> {
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
    idxs: Vec<usize>, // VarId : -> order : usize
}

pub trait AccessHeap {
    fn get_root(&self, heap: &mut VarIdHeap) -> VarId;
}

impl<'a> AccessHeap for Vec<Var> {
    fn get_root(&self, heap: &mut VarIdHeap) -> VarId {
        heap.root(self)
    }
}

pub trait VarOrdering {
    fn reset(&mut self) -> ();
    fn contains(&self, v: VarId) -> bool;
    fn update(&mut self, vec: &[Var], v: VarId) -> ();
    fn insert(&mut self, vec: &[Var], v: VarId) -> ();
    fn root(&mut self, vec: &[Var]) -> VarId;
    fn is_empty(&self) -> bool;
    fn clear(&mut self) -> ();
    fn len(&self) -> usize;
    fn peek(&self) -> VarId;
}

impl VarOrdering for VarIdHeap {
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
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
    fn clear(&mut self) -> () {
        self.reset()
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn peek(&self) -> VarId {
        self.heap[1]
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
        VarIdHeap { order, heap, idxs }
    }
    /// renamed form numElementsInHeap
    pub fn len(&self) -> usize {
        self.idxs[0]
    }
    fn percolate_up(&mut self, vec: &[Var], start: usize) -> () {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = match self.order {
            VarOrder::ByActivity => vec[vq].activity,
            VarOrder::ByOccurence => (vec[vq].pos_occurs.len() + vec[vq].neg_occurs.len()) as f64,
        };
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = match self.order {
                    VarOrder::ByActivity => vec[vp].activity,
                    VarOrder::ByOccurence => (vec[vp].pos_occurs.len() + vec[vp].neg_occurs.len()) as f64,
                };
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
    fn percolate_down(&mut self, vec: &[Var], start: usize) -> () {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i];
        let ai = match self.order {
            VarOrder::ByActivity => vec[vi].activity,
            VarOrder::ByOccurence => (vec[vi].pos_occurs.len() + vec[vi].neg_occurs.len()) as f64,
        };
        loop {
            let l = 2 * i; // left
            if l <= n {
                let r = l + 1; // right
                let vl = self.heap[l];
                let vr = self.heap[r];
                let al = match self.order {
                    VarOrder::ByActivity => vec[vl].activity,
                    VarOrder::ByOccurence => (vec[vi].pos_occurs.len() + vec[vi].neg_occurs.len()) as f64,
                };
                let ar = match self.order {
                    VarOrder::ByActivity => vec[vr].activity,
                    VarOrder::ByOccurence => (vec[vr].pos_occurs.len() + vec[vr].neg_occurs.len()) as f64,
                };
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
    pub fn dump(&self) -> () {
        println!("# - heap {:?}", self.heap);
        println!("# - idxs {:?}", self.idxs);
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

/// Literal eliminator
#[derive(Debug)]
pub struct Eliminator {
    pub merges: usize,
    /// renamed elimHeap. FIXME: can we use VarIdHeap here?
    pub var_queue: Vec<VarId>,
    pub n_touched: usize,
    pub asymm_lits: usize,
    pub clause_queue: Vec<ClauseId>,
    pub binclause_queue: Vec<ClauseId>,
    pub bwdsub_assigns: usize,
    //    pub bwdsub_tmp_unit: ClauseId,
    pub bwdsub_tmp_clause: Clause,
    pub remove_satisfied: bool,
    // working place
    pub merge_vec: Vec<Lit>,
    pub elim_clauses: Vec<Lit>,
    /// Variables are not eliminated if it produces a resolvent with a length above this limit.
    /// 0 means no limit.
    pub clause_lim: usize,
    pub eliminated_vars: usize,
    pub add_tmp: Vec<Lit>,
    pub use_elim: bool,
    pub turn_off_elim: bool,
    pub use_simplification: bool,
    pub subsumption_lim: usize,
    pub targets: Vec<ClauseId>,
    pub subsume_clause_size: usize,
    pub last_invocatiton: usize,
}

impl Eliminator {
    pub fn new(use_elim: bool, nv: usize) -> Eliminator {
        // let heap = VarIdHeap::new(VarOrder::ByOccurence, nv, 0);
        let mut bwdsub_tmp_clause = Clause::null();
        bwdsub_tmp_clause.index = BWDSUB_CLAUSE;
        Eliminator {
            merges: 0,
            var_queue: Vec::new(),
            n_touched: 0,
            asymm_lits: 0,
            clause_queue: Vec::new(),
            binclause_queue: Vec::new(),
            bwdsub_assigns: 0,
            //            bwdsub_tmp_unit: 0,
            bwdsub_tmp_clause,
            remove_satisfied: false,
            merge_vec: vec![0; nv + 1],
            elim_clauses: Vec::new(),
            clause_lim: 20,
            eliminated_vars: 0,
            add_tmp: Vec::new(),
            use_elim,
            turn_off_elim: false,
            use_simplification: true,
            subsumption_lim: 0,
            targets: Vec::new(),
            subsume_clause_size: SUBSUMPTION_SIZE,
            last_invocatiton: 0,
        }
    }
}

impl Dump for Eliminator {
    fn dump(&self, str: &str) -> () {
        println!("{}", str);
        println!(" - n_touched {}", self.n_touched);
        println!(" - clause_queue {:?}", self.clause_queue);
        println!(" - heap {:?}", self.var_queue);
    }
}

#![allow(unused_imports)]
use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::DEAD_CLAUSE;
use types::*;

/// for &'a[Var]
pub trait Satisfiability {
    fn assigned(&self, l: Lit) -> Lbool;
    fn satisfies(&self, c: &Clause) -> bool;
}

/// for VarIdHeap
pub trait HeapManagement {
    fn new(n: usize, init: usize) -> VarIdHeap;
    fn select_var(&mut self, assign: &[Lbool], vars: &[Var]) -> VarId;
    fn bump(&mut self, vars: &mut [Var], vi: VarId, d: f64) -> ();
    fn rebuild(&mut self, assign: &[Lbool], vars: &[Var]) -> ();
    fn reset(&mut self) -> ();
    fn contains(&self, v: VarId) -> bool;
    fn update(&mut self, vec: &[Var], v: VarId) -> ();
    fn insert(&mut self, vec: &[Var], v: VarId) -> ();
    fn delete(&mut self, vec: &[Var], vi: VarId) -> ();
    fn get_root(&mut self, vec: &[Var]) -> VarId;
    fn is_empty(&self) -> bool;
    fn len(&self) -> usize;
    fn peek(&self) -> VarId;
}

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;
const BWDSUB_CLAUSE: ClauseId = DEAD_CLAUSE - 1;
const SUBSUMPTION_SIZE: usize = 20;
/// is the dummy var index.
pub const NULL_VAR: VarId = 0;

/// Struct for a variable.
#[derive(Debug)]
pub struct Var {
    pub index: usize,
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

impl<'a> Satisfiability for &'a[Lbool] {
    fn assigned(&self, l: Lit) -> Lbool {
        self[l.vi()] ^ ((l & 1) as u8)
    }
    fn satisfies(&self, c: &Clause) -> bool {
        for l in &c.lit {
            if self.assigned(*l) == LTRUE {
                return true;
            }
        }
        for l in &c.lits {
            if self.assigned(*l) == LTRUE {
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
    pub heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
}

impl HeapManagement for VarIdHeap {
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
    }
    fn delete(&mut self, vec: &[Var], vs: VarId) -> () {
        let s = self.idxs[vs];
        let n = self.idxs[0];
        let vn = self.heap[n];
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if s < self.idxs[0] {
            self.percolate_down(&vec, s);
        }
    }
    /// renamed from getHeapDown
    fn get_root(&mut self, vec: &[Var]) -> VarId {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n];
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vec, 1);
        }
        vs
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn peek(&self) -> VarId {
        self.heap[1]
    }
    fn rebuild(&mut self, assign: &[Lbool], vars: &[Var]) -> () {
        self.reset();
        for (vi, val) in assign.iter().enumerate().skip(1) {
            if *val == BOTTOM {
                self.insert(&vars, vi);
            }
        }
    }
    fn bump(&mut self, vars: &mut [Var], vi: VarId, d: f64) -> () {
        let a = (vars[vi].activity + d) / 2.0;
        vars[vi].activity = a;
        if VAR_ACTIVITY_THRESHOLD < a {
            for v in &mut vars[1..] {
                v.activity /= VAR_ACTIVITY_THRESHOLD;
            }
        }
        self.update(vars, vi);
    }
    /// Heap operations; renamed from selectVO
    fn select_var(&mut self, assign: &[Lbool], vars: &[Var]) -> VarId {
        // let mut best = 0;
        // let mut act = 0.0;
        // for v in &vars[1..] {
        //     if assign[v.index] == BOTTOM && act < v.activity {
        //         best = v.index;
        //         act = v.activity;
        //     }
        // }
        // return best;
        loop {
            if self.len() == 0 {
                return 0;
            }
            let vi = self.get_root(&vars);
            if assign[vi] == BOTTOM {
                return vi;
            }
        }
    }
    fn new(n: usize, init: usize) -> VarIdHeap {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(init);
        for i in 1..n + 1 {
            heap.push(i);
            idxs.push(i);
        }
        VarIdHeap { heap, idxs }
    }
}

impl VarIdHeap {
    fn percolate_up(&mut self, vec: &[Var], start: usize) -> () {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = vec[vq].activity;
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vec[vp].activity;
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
        let ai = vec[vi].activity;
        loop {
            let l = 2 * i; // left
            if l <= n {
                let r = l + 1; // right
                let vl = self.heap[l];
                let vr = self.heap[r];
                let al = vec[vl].activity;
                let ar = vec[vr].activity;
                let (best, vc, ac) = if r <= n && al < ar {
                    (r, vr, ar)
                } else {
                    (l, vl, al)
                };
                if ai < ac {
                    self.heap[i] = vc;
                    self.idxs[vc] = i;
                    i = best;
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

impl VarIdHeap {
    pub fn validate(&self, assign: &[Lbool], vars: &[Var]) -> () {
        if self.idxs[0] == 0 {
            return;
        }
        let vi = self.heap[1];
        if assign[vi] != BOTTOM {
            panic!("top of heap are assigned!");
        }
        let act = vars[vi].activity;
        let mut cnt = 0;
        for i in 1..vars.len() {
            if assign[i] == BOTTOM && act < vars[i].activity {
                cnt += 1;
            }
        }
        if 0 < cnt {
            panic!("not best {} < {}", act, cnt);
        }
        println!("pass");
    }
}

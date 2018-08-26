use types::*;

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
}

/// is the dummy var index.
pub const NULL_VAR: VarIndex = 0;

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

pub trait VarOrdering {
    fn reset(&mut self) -> ();
    fn update(&mut self, vec: &[Var], v: VarIndex) -> ();
    fn insert(&mut self, vec: &[Var], v: VarIndex) -> ();
    fn root(&mut self, vec: &[Var]) -> VarIndex;
}

impl VarOrdering for VarIndexHeap {
    fn reset(&mut self) -> () {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    /// renamed from incrementHeap, updateVO
    fn update(&mut self, vec: &[Var], v: VarIndex) -> () {
        debug_assert!(v != 0, "Invalid VarIndex");
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(vec, start)
        }
    }
    /// renamed from undoVO
    fn insert(&mut self, vec: &[Var], vi: VarIndex) -> () {
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
    fn root(&mut self, vec: &[Var]) -> VarIndex {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n];
        // self.var_order.check(&format!("root 1 :[({}, {}) ({}, {})]", s, vs, n, vn));
        debug_assert!(vn != 0, "Invalid VarIndex for heap");
        debug_assert!(vs != 0, "Invalid VarIndex for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vec, 1);
        }
        // self.var_order.check("root 2");
        vs
    }
}

impl VarIndexHeap {
    pub fn new(n: usize) -> VarIndexHeap {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(n);
        for i in 1..n + 1 {
            heap.push(i);
            idxs.push(i);
        }
        VarIndexHeap { heap, idxs }
    }
    /// renamed form numElementsInHeap
    pub fn len(&self) -> usize {
        self.idxs[0]
    }
    /// renamed from inHeap
    fn contains(&self, v: VarIndex) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
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

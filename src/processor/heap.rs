/// Module `eliminator` implements clause subsumption and var elimination.
use {
    crate::{assign::AssignIF, types::*, var_vector::*},
    std::fmt,
};

pub trait VarOrderIF {
    fn clear(&mut self, asg: &mut impl AssignIF);
    fn len(&self) -> usize;
    fn insert(&mut self, occur: &[LitOccurs], vi: VarId, upward: bool);
    fn is_empty(&self) -> bool;
    fn select_var(&mut self, occur: &[LitOccurs], asg: &impl AssignIF) -> Option<VarId>;
    #[allow(dead_code)]
    fn rebuild(&mut self, asg: &impl AssignIF, occur: &[LitOccurs]);
}

/// Mapping from Literal to Clauses.
#[derive(Clone, Debug, Default)]
pub struct LitOccurs {
    pub aborted: bool,
    pub pos_occurs: Vec<ClauseId>,
    pub neg_occurs: Vec<ClauseId>,
}

impl LitOccurs {
    /// return a new vector of $n$ `LitOccurs`s.
    pub fn new(n: usize) -> Vec<LitOccurs> {
        let mut vec = Vec::with_capacity(n + 1);
        for _ in 0..=n {
            vec.push(LitOccurs::default());
        }
        vec
    }
    pub fn clear(&mut self) {
        self.aborted = false;
        self.pos_occurs.clear();
        self.neg_occurs.clear();
    }
    pub fn activity(&self) -> usize {
        if self.aborted {
            usize::MAX
        } else {
            self.pos_occurs.len().min(self.neg_occurs.len())
        }
    }
    pub fn is_empty(&self) -> bool {
        self.pos_occurs.is_empty() && self.neg_occurs.is_empty()
    }
    pub fn len(&self) -> usize {
        self.pos_occurs.len() + self.neg_occurs.len()
    }
}

/// Var heap structure based on the number of occurrences
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - `idxs[0]` contains the number of alive elements
///   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Clone, Debug)]
pub struct VarOccHeap {
    pub heap: Vec<u32>, // order : usize -> VarId::from
    pub idxs: Vec<u32>, // VarId : -> order : usize::from
}

impl VarOccHeap {
    pub fn new(n: usize, init: usize) -> Self {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(n as u32);
        for i in 1..=n {
            heap.push(i as u32);
            idxs.push(i as u32);
        }
        idxs[0] = init as u32;
        VarOccHeap { heap, idxs }
    }
}

impl VarOrderIF for VarOccHeap {
    fn insert(&mut self, occur: &[LitOccurs], vi: VarId, upward: bool) {
        debug_assert!(vi < self.heap.len());
        if self.contains(vi) {
            let i = self.idxs[vi];
            if upward {
                self.percolate_up(occur, i);
            } else {
                self.percolate_down(occur, i);
            }
            return;
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n as usize];
        self.heap.swap(i as usize, n as usize);
        self.idxs.swap(vi, vn as usize);
        debug_assert!((n as usize) < self.heap.len());
        self.idxs[0] = n;
        self.percolate_up(occur, n);
    }
    fn clear(&mut self, _asg: &mut impl AssignIF) {
        for v in &mut self.heap[0..self.idxs[0] as usize] {
            // asg.var_mut(*v as usize).turn_off(FlagVar::ENQUEUED);
            VarRef(*v as usize).turn_off(FlagVar::ENQUEUED);
        }
        self.reset()
    }
    fn len(&self) -> usize {
        self.idxs[0] as usize
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
    fn select_var(&mut self, occur: &[LitOccurs], _asg: &impl AssignIF) -> Option<VarId> {
        loop {
            let vi = self.get_root(occur);
            if vi == 0 {
                return None;
            }
            if !VarRef(vi).is(FlagVar::ELIMINATED) {
                return Some(vi);
            }
        }
    }
    fn rebuild(&mut self, _asg: &impl AssignIF, occur: &[LitOccurs]) {
        self.reset();
        for vi in VarRef::var_id_iter() {
            if VarRef(vi).assign().is_none() && !VarRef(vi).is(FlagVar::ELIMINATED) {
                self.insert(occur, vi, true);
            }
        }
    }
}

impl VarOccHeap {
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn reset(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i as u32;
            self.heap[i] = i as u32;
        }
    }
    fn get_root(&mut self, occur: &[LitOccurs]) -> VarId {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        debug_assert!((n as usize) < self.heap.len());
        if n == 0 {
            return 0;
        }
        let vn = self.heap[n as usize];
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n as usize, s);
        self.idxs.swap(vn as usize, vs as usize);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(occur, 1);
        }
        vs as usize
    }
    fn percolate_up(&mut self, occur: &[LitOccurs], start: u32) {
        let mut q = start;
        let vq = self.heap[q as usize];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = occur[vq as usize].activity();
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q as usize] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq as usize] = q;
                return;
            } else {
                let vp = self.heap[p as usize];
                let ap = occur[vp as usize].activity();
                if ap > aq {
                    // move down the current parent, and make it empty
                    self.heap[q as usize] = vp;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vp as usize] = q;
                    q = p;
                } else {
                    self.heap[q as usize] = vq;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vq as usize] = q;
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, occur: &[LitOccurs], start: u32) {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i as usize];
        let ai = occur[vi as usize].activity();
        loop {
            let l = 2 * i; // left
            if l < (n as u32) {
                let vl = self.heap[l as usize];
                let al = occur[vl as usize].activity();
                let r = l + 1; // right
                let (target, vc, ac) =
                    if r < (n as u32) && al > occur[self.heap[r as usize] as usize].activity() {
                        let vr = self.heap[r as usize];
                        (r, vr, occur[vr as usize].activity())
                    } else {
                        (l, vl, al)
                    };
                if ai > ac {
                    self.heap[i as usize] = vc;
                    self.idxs[vc as usize] = i;
                    i = target;
                } else {
                    self.heap[i as usize] = vi;
                    debug_assert!(vi != 0, "invalid index");
                    self.idxs[vi as usize] = i;
                    return;
                }
            } else {
                self.heap[i as usize] = vi;
                debug_assert!(vi != 0, "invalid index");
                self.idxs[vi as usize] = i;
                return;
            }
        }
    }
    /* #[allow(dead_code)]
    fn peek(&self) -> VarId {
        self.heap[1]
    }
    #[allow(dead_code)]
    fn remove(&mut self, occur: &[LitOccurs], vs: VarId) {
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
            self.percolate_down(occur, 1);
        }
    }
    #[allow(dead_code)]
    fn check(&self, s: &str) {
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
    } */
}

impl fmt::Display for VarOccHeap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            " - seek pointer - nth -> var: {:?}\n - var -> nth: {:?}",
            self.heap, self.idxs,
        )
    }
}

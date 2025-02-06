///
/// Heap struct for selecting decision vars
///
use {super::stack::AssignStack, crate::types::*, std::fmt};

#[cfg(feature = "trail_saving")]
use super::TrailSavingIF;

/// Heap of VarId, based on var activity.
// # Note
// - both fields has a fixed length. Don't use push and pop.
// - `idxs[0]` contains the number of alive elements
//   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Clone, Debug, Default)]
pub struct VarIdHeap {
    /// order : usize -> VarId::from, -- Which var is the n-th best?
    heap: Vec<u32>,
    /// VarId : -> order : usize::from -- How good is the var?
    /// `idxs[0]` holds the number of alive elements
    idxs: Vec<u32>,
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

impl VarIdHeap {
    pub fn new(n: usize) -> Self {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(n as u32);
        for i in 1..=n {
            heap.push(i as u32);
            idxs.push(i as u32);
        }
        idxs[0] = n as u32;
        VarIdHeap { heap, idxs }
    }
}

/// Internal heap manipulation API
pub trait VarHeapIF {
    fn clear_heap(&mut self);
    fn expand_heap(&mut self);
    fn insert_heap(&mut self, vi: VarId);
    fn update_heap(&mut self, v: VarId);
    fn get_heap_root(&mut self) -> VarId;
    fn percolate_up(&mut self, start: u32);
    fn percolate_down(&mut self, start: u32);
    fn remove_from_heap(&mut self, vs: VarId);
}

/* impl VarHeapIF for AssignStack {
    fn clear_heap(&mut self) {
        self.var_order.clear();
    }
    fn expand_heap(&mut self) {
        // Fill a new slot with the value that would be used in VarIdHeap::new.
        let id = self.var_order.heap.len() as u32;
        self.var_order.heap.push(id);
        self.var_order.idxs.push(id);
    }
    fn update_heap(&mut self, v: VarId) {
        debug_assert!(v != 0, "Invalid VarId");
        let start = self.var_order.idxs[v];
        if self.var_order.contains(v) {
            self.percolate_up(start);
        }
    }
    fn insert_heap(&mut self, vi: VarId) {
        let i = self.var_order.insert(vi);
        self.percolate_up(i as u32);
    }
    fn get_heap_root(&mut self) -> VarId {
        #[cfg(feature = "trail_saving")]
        if self.var_order.is_empty() {
            self.clear_saved_trail();
        }
        let vs = self.var_order.get_root();
        if 1 < self.var_order.len() {
            self.percolate_down(1);
        }
        vs
    }
    fn percolate_up(&mut self, start: u32) {
        let mut q = start;
        let vq = self.var_order.heap[q as usize];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = self.activity(vq as usize);
        loop {
            let p = q / 2;
            if p == 0 {
                self.var_order.heap[q as usize] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.var_order.idxs[vq as usize] = q;
                return;
            } else {
                let vp = self.var_order.heap[p as usize];
                let ap = self.activity(vp as usize);
                if ap < aq {
                    // move down the current parent, and make it empty
                    self.var_order.heap[q as usize] = vp;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.var_order.idxs[vp as usize] = q;
                    q = p;
                } else {
                    self.var_order.heap[q as usize] = vq;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.var_order.idxs[vq as usize] = q;
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, start: u32) {
        let n = self.var_order.len();
        let mut i = start;
        let vi = self.var_order.heap[i as usize];
        let ai = self.activity(vi as usize);
        loop {
            let l = 2 * i; // left
            if l < n as u32 {
                let vl = self.var_order.heap[l as usize];
                let al = self.activity(vl as usize);
                let r = l + 1; // right
                let (target, vc, ac) = if r < (n as u32)
                    && al < self.activity(self.var_order.heap[r as usize] as usize)
                {
                    let vr = self.var_order.heap[r as usize];
                    (r, vr, self.activity(vr as usize))
                } else {
                    (l, vl, al)
                };
                if ai < ac {
                    self.var_order.heap[i as usize] = vc;
                    self.var_order.idxs[vc as usize] = i;
                    i = target;
                } else {
                    self.var_order.heap[i as usize] = vi;
                    debug_assert!(vi != 0, "invalid index");
                    self.var_order.idxs[vi as usize] = i;
                    return;
                }
            } else {
                self.var_order.heap[i as usize] = vi;
                debug_assert!(vi != 0, "invalid index");
                self.var_order.idxs[vi as usize] = i;
                return;
            }
        }
    }
    fn remove_from_heap(&mut self, vi: VarId) {
        if let Some(i) = self.var_order.remove(vi) {
            self.percolate_down(i as u32);
        }
    }
}*/

trait VarOrderIF {
    fn clear(&mut self);
    fn contains(&self, v: VarId) -> bool;
    fn get_root(&mut self) -> VarId;
    fn len(&self) -> usize;
    fn insert(&mut self, vi: VarId) -> usize;
    fn is_empty(&self) -> bool;
    fn remove(&mut self, vi: VarId) -> Option<usize>;
}

impl VarOrderIF for VarIdHeap {
    fn clear(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i as u32;
            self.heap[i] = i as u32;
        }
    }
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn get_root(&mut self) -> VarId {
        let s: usize = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n as usize];
        debug_assert!(vn != 0, "Invalid VarId for heap: vn {vn}, n {n}");
        debug_assert!(vs != 0, "Invalid VarId for heap: vs {vs}, n {n}");
        self.heap.swap(n as usize, s);
        self.idxs.swap(vn as usize, vs as usize);
        self.idxs[0] -= 1;
        vs as VarId
    }
    fn len(&self) -> usize {
        self.idxs[0] as usize
    }
    #[allow(clippy::unnecessary_cast)]
    fn insert(&mut self, vi: VarId) -> usize {
        if self.contains(vi) {
            return self.idxs[vi as usize] as usize;
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n as usize];
        self.heap.swap(i as usize, n as usize);
        self.idxs.swap(vi, vn as usize);
        self.idxs[0] = n;
        n as usize
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
    fn remove(&mut self, vi: VarId) -> Option<usize> {
        let i = self.idxs[vi];
        let n = self.idxs[0];
        debug_assert_ne!(i, 0);
        if n < i {
            return None;
        }
        let vn = self.heap[n as usize];
        self.heap.swap(n as usize, i as usize);
        self.idxs.swap(vn as usize, vi);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            return Some(i as usize);
        }
        None
    }
}

impl VarIdHeap {
    #[allow(dead_code)]
    fn peek(&self) -> VarId {
        self.heap[1] as VarId
    }
    #[allow(dead_code)]
    fn check(&self, s: &str) {
        let h = &mut self.heap.clone()[1..];
        let d = &mut self.idxs.clone()[1..];
        h.sort_unstable();
        d.sort_unstable();
        for i in 0..h.len() {
            if h[i] != i as u32 + 1 {
                panic!("heap {} {} {:?}", i, h[i], h);
            }
            if d[i] != i as u32 + 1 {
                panic!("idxs {} {} {:?}", i, d[i], d);
            }
        }
        println!(" - pass var_order test at {s}");
    }
}

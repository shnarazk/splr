/// Heap struct for selecting decision vars
use {
    super::{AssignStack, VarIdHeap},
    crate::types::*,
    std::fmt,
};

impl Default for VarIdHeap {
    fn default() -> VarIdHeap {
        VarIdHeap {
            heap: Vec::new(),
            idxs: Vec::new(),
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

/// Internal heap manipulation API
pub trait VarHeapIF {
    fn clear_heap(&mut self);
    fn expand_heap(&mut self);
    fn insert_heap(&mut self, vi: VarId);
    fn update_heap(&mut self, v: VarId);
    fn get_heap_root(&mut self) -> VarId;
    fn percolate_up(&mut self, start: usize);
    fn percolate_down(&mut self, start: usize);
    fn remove_from_heap(&mut self, vs: VarId);
}

impl VarHeapIF for AssignStack {
    fn clear_heap(&mut self) {
        self.var_order.clear();
    }
    fn expand_heap(&mut self) {
        self.var_order.heap.push(0);
        self.var_order.idxs.push(0);
        self.var_order.clear();
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
        self.percolate_up(i);
    }
    fn get_heap_root(&mut self) -> VarId {
        let vs = self.var_order.get_root();
        if 1 < self.var_order.len() {
            self.percolate_down(1);
        }
        vs
    }
    fn percolate_up(&mut self, start: usize) {
        let mut q = start;
        let vq = self.var_order.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = self.activity(vq);
        loop {
            let p = q / 2;
            if p == 0 {
                self.var_order.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.var_order.idxs[vq] = q;
                return;
            } else {
                let vp = self.var_order.heap[p];
                let ap = self.activity(vp);
                if ap < aq {
                    // move down the current parent, and make it empty
                    self.var_order.heap[q] = vp;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.var_order.idxs[vp] = q;
                    q = p;
                } else {
                    self.var_order.heap[q] = vq;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.var_order.idxs[vq] = q;
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, start: usize) {
        let n = self.var_order.len();
        let mut i = start;
        let vi = self.var_order.heap[i];
        let ai = self.activity(vi);
        loop {
            let l = 2 * i; // left
            if l < n {
                let vl = self.var_order.heap[l];
                let al = self.activity(vl);
                let r = l + 1; // right
                let (target, vc, ac) = if r < n && al < self.activity(self.var_order.heap[r]) {
                    let vr = self.var_order.heap[r];
                    (r, vr, self.activity(vr))
                } else {
                    (l, vl, al)
                };
                if ai < ac {
                    self.var_order.heap[i] = vc;
                    self.var_order.idxs[vc] = i;
                    i = target;
                } else {
                    self.var_order.heap[i] = vi;
                    debug_assert!(vi != 0, "invalid index");
                    self.var_order.idxs[vi] = i;
                    return;
                }
            } else {
                self.var_order.heap[i] = vi;
                debug_assert!(vi != 0, "invalid index");
                self.var_order.idxs[vi] = i;
                return;
            }
        }
    }
    fn remove_from_heap(&mut self, vi: VarId) {
        if let Some(i) = self.var_order.remove(vi) {
            self.percolate_down(i);
        }
    }
}

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
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn get_root(&mut self) -> VarId {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n];
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        vs
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn insert(&mut self, vi: VarId) -> usize {
        if self.contains(vi) {
            return self.idxs[vi];
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n];
        self.heap.swap(i, n);
        self.idxs.swap(vi, vn);
        self.idxs[0] = n;
        return n;
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
        let vn = self.heap[n];
        self.heap.swap(n, i);
        self.idxs.swap(vn, vi);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            return Some(i);
        }
        None
    }
}

impl VarIdHeap {
    #[allow(dead_code)]
    fn peek(&self) -> VarId {
        self.heap[1]
    }
    #[allow(dead_code)]
    fn check(&self, s: &str) {
        let h = &mut self.heap.clone()[1..];
        let d = &mut self.idxs.clone()[1..];
        h.sort_unstable();
        d.sort_unstable();
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

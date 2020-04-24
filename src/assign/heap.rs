/// Heap struct for selecting decision vars
use {
    super::{AssignStack, VarIdHeap, VarRewardIF},
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

pub trait VarHeapIF {
    fn update_heap(&mut self, v: VarId);
    fn insert_heap(&mut self, vi: VarId);
    fn get_heap_root(&mut self) -> VarId;
    fn percolate_up(&mut self, start: usize);
    fn percolate_down(&mut self, start: usize);
    fn remove(&mut self, vs: VarId);
}

impl VarHeapIF for AssignStack {
    fn update_heap(&mut self, v: VarId) {
        debug_assert!(v != 0, "Invalid VarId");
        let start = self.var_order.idxs[v];
        if self.var_order.contains(v) {
            self.percolate_up(start);
        }
    }
    fn insert_heap(&mut self, vi: VarId) {
        if self.var_order.contains(vi) {
            let i = self.var_order.idxs[vi];
            self.percolate_up(i);
            return;
        }
        let i = self.var_order.idxs[vi];
        let n = self.var_order.idxs[0] + 1;
        let vn = self.var_order.heap[n];
        self.var_order.heap.swap(i, n);
        self.var_order.idxs.swap(vi, vn);
        self.var_order.idxs[0] = n;
        self.percolate_up(n);
    }
    fn get_heap_root(&mut self) -> VarId {
        let s = 1;
        let vs = self.var_order.heap[s];
        let n = self.var_order.idxs[0];
        let vn = self.var_order.heap[n];
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.var_order.heap.swap(n, s);
        self.var_order.idxs.swap(vn, vs);
        self.var_order.idxs[0] -= 1;
        if 1 < self.var_order.idxs[0] {
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
    #[allow(dead_code)]
    fn remove(&mut self, vs: VarId) {
        let s = self.var_order.idxs[vs];
        let n = self.var_order.idxs[0];
        if n < s {
            return;
        }
        let vn = self.var_order.heap[n];
        self.var_order.heap.swap(n, s);
        self.var_order.idxs.swap(vn, vs);
        self.var_order.idxs[0] -= 1;
        if 1 < self.var_order.idxs[0] {
            self.percolate_down(1);
        }
    }
}

pub trait VarOrderIF {
    fn new(n: usize, init: usize) -> VarIdHeap;
    fn clear(&mut self);
    fn contains(&self, v: VarId) -> bool;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
}

impl VarOrderIF for VarIdHeap {
    fn new(n: usize, init: usize) -> VarIdHeap {
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
    fn clear(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
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

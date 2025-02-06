#![allow(static_mut_refs)]

#[cfg(feature = "trail_saving")]
use crate::assign::TrailSavingIF;

use crate::{assign::AssignStack, types::*, var_vector::*};

pub struct VarActivityManager {
    decay: f64,
    anti_decay: f64,
    tick: usize,
}

pub static mut VAM: VarActivityManager = VarActivityManager {
    decay: 0.95,
    anti_decay: 0.05,
    tick: 0,
};

static mut VAR_HEAP: VarIdHeap = VarIdHeap {
    heap: Vec::new(),
    idxs: Vec::new(),
};

impl VarActivityManager {
    pub fn initialize() {
        unsafe {
            VAR_HEAP.clear();
            let new_heap = VarIdHeap::new(VarRef::num_vars());
            VAR_HEAP = new_heap;
        }
    }
    pub fn set_activity_decay(decay: f64) {
        unsafe {
            VAM.decay = decay;
            VAM.anti_decay = 1.0 - decay;
        }
    }
    pub fn update_var_activity(vi: VarId) {
        unsafe {
            VarRef(vi).update_activity(VAM.decay, VAM.anti_decay);
        }
    }
    pub fn reward_at_analysis(vi: VarId) {
        // self.var[vi].turn_on(FlagVar::USED);
        VarRef(vi).turn_on(FlagVar::USED);
    }
    #[inline]
    pub fn reward_at_assign(_vi: VarId) {}
    #[inline]
    pub fn reward_at_propagation(_vi: VarId) {}
    #[inline]
    pub fn reward_at_unassign(vi: VarId) {
        unsafe {
            VarRef(vi).update_activity(VAM.decay, VAM.anti_decay);
        }
    }
    pub fn clear_heap() {
        unsafe {
            VAR_HEAP.clear();
        }
    }
    pub fn insert_var(vi: VarId) {
        unsafe {
            VAR_HEAP.insert_heap(vi, VarRef(vi).reward());
        }
    }
    pub fn remove_var(vi: VarId) {
        unsafe {
            VAR_HEAP.remove_from_heap(vi);
        }
    }
    pub fn update_heap(vi: VarId) {
        unsafe {
            VAR_HEAP.update_heap(vi);
        }
    }
    pub fn pop_top_var(asg: &mut AssignStack) -> VarId {
        unsafe { VAR_HEAP.get_heap_root(asg) }
    }
    pub fn add_var() {
        unsafe {
            VAR_HEAP.expand_heap();
        }
    }
    pub fn increment_tick() {
        unsafe {
            VAM.tick += 1;
        }
    }
}

//
// Heap struct for selecting decision vars
//
// use {super::stack::AssignStack, crate::types::*, std::fmt};

// #[cfg(feature = "trail_saving")]
// use super::TrailSavingIF;

/// Heap of VarId, based on var activity.
// # Note
// - both fields has a fixed length. Don't use push and pop.
// - `idxs[0]` contains the number of alive elements
//   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Clone, Debug, Default)]
struct VarIdHeap {
    /// order : usize -> VarId::from, -- Which var is the n-th best?
    heap: Vec<OrderedProxy<VarId>>,
    /// VarId : -> order : usize::from -- How good is the var?
    /// `idxs[0]` holds the number of alive elements
    idxs: Vec<u32>,
}

// impl fmt::Display for VarIdHeap {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(
//             f,
//             " - seek pointer - nth -> var: {:?}\n - var -> nth: {:?}",
//             self.heap, self.idxs,
//         )
//     }
// }

impl VarIdHeap {
    pub fn new(n: usize) -> Self {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(OrderedProxy::new(VarId::default(), 0.0));
        idxs.push(n as u32);
        for i in 1..=n {
            heap.push(OrderedProxy::new(i as VarId, 0.0));
            idxs.push(i as u32);
        }
        idxs[0] = n as u32;
        VarIdHeap { heap, idxs }
    }
}

/// Internal heap manipulation API
trait VarHeapIF {
    fn expand_heap(&mut self);
    fn insert_heap(&mut self, vi: VarId, activity: f64);
    fn update_heap(&mut self, v: VarId);
    fn get_heap_root(&mut self, asg: &mut AssignStack) -> VarId;
    fn percolate_up(&mut self, start: u32);
    fn percolate_down(&mut self, start: u32);
    fn remove_from_heap(&mut self, vi: VarId);
}

impl VarHeapIF for VarIdHeap {
    fn expand_heap(&mut self) {
        // Fill a new slot with the value that would be used in VarIdHeap::new.
        let id = self.heap.len() as VarId;
        self.heap.push(OrderedProxy::new(id, 0.0));
        self.idxs.push(id as u32);
    }
    fn insert_heap(&mut self, vi: VarId, activity: f64) {
        let i = self.insert(vi, activity);
        self.percolate_up(i as u32);
    }
    fn update_heap(&mut self, v: VarId) {
        debug_assert!(v != 0, "Invalid VarId");
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(start);
        }
    }
    fn get_heap_root(&mut self, asg: &mut AssignStack) -> VarId {
        #[cfg(feature = "trail_saving")]
        if self.is_empty() {
            asg.clear_saved_trail();
        }
        let vs = self.get_root();
        if 1 < self.len() {
            self.percolate_down(1);
        }
        vs
    }
    fn percolate_up(&mut self, start: u32) {
        let mut q = start;
        let vq_body = self.heap[q as usize].body;
        let vq_index = self.heap[q as usize].index;
        debug_assert!(0 < vq_body, "size of heap is too small");
        let aq = vq_index;
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q as usize].body = vq_body;
                self.heap[q as usize].index = vq_index;
                debug_assert!(vq_body != 0, "Invalid index in percolate_up");
                self.idxs[vq_body] = q;
                return;
            } else {
                let vp_body = self.heap[p as usize].body;
                let vp_index = self.heap[p as usize].index;
                let ap = vp_index;
                if ap < aq {
                    // move down the current parent, and make it empty
                    self.heap[q as usize].body = vp_body;
                    self.heap[q as usize].index = vp_index;
                    debug_assert!(vq_body != 0, "Invalid index in percolate_up");
                    self.idxs[vp_body] = q;
                    q = p;
                } else {
                    self.heap[q as usize].body = vq_body;
                    self.heap[q as usize].index = vq_index;
                    debug_assert!(vq_body != 0, "Invalid index in percolate_up");
                    self.idxs[vq_body] = q;
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, start: u32) {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i as usize].body;
        let ai = self.heap[i as usize].index;
        loop {
            let l = 2 * i; // left
            if l < n as u32 {
                let vl = self.heap[l as usize].body;
                let al = self.heap[l as usize].index;
                let r = l + 1; // right
                let (target, vc, ac) = if r < (n as u32) && al < self.heap[r as usize].index {
                    (r, self.heap[r as usize].body, self.heap[r as usize].index)
                } else {
                    (l, vl, al)
                };
                if ai < ac {
                    self.heap[i as usize].body = vc;
                    self.heap[i as usize].index = ac;
                    self.idxs[vc as usize] = i;
                    i = target;
                } else {
                    self.heap[i as usize].body = vi;
                    self.heap[i as usize].index = ai;
                    debug_assert!(vi != 0, "invalid index");
                    self.idxs[vi as usize] = i;
                    return;
                }
            } else {
                self.heap[i as usize].body = vi;
                self.heap[i as usize].index = ai;
                debug_assert!(vi != 0, "invalid index");
                self.idxs[vi as usize] = i;
                return;
            }
        }
    }
    fn remove_from_heap(&mut self, vi: VarId) {
        if let Some(i) = self.remove(vi) {
            self.percolate_down(i as u32);
        }
    }
}

trait VarOrderIF {
    fn clear(&mut self);
    fn contains(&self, v: VarId) -> bool;
    fn get_root(&mut self) -> VarId;
    fn len(&self) -> usize;
    fn insert(&mut self, vi: VarId, activity: f64) -> usize;
    fn is_empty(&self) -> bool;
    fn remove(&mut self, vi: VarId) -> Option<usize>;
}

impl VarOrderIF for VarIdHeap {
    fn clear(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i as u32;
            self.heap[i].index = 0.0;
            self.heap[i].body = i as VarId;
        }
    }
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn get_root(&mut self) -> VarId {
        let s: usize = 1;
        let vs = self.heap[s].to();
        let n = self.idxs[0];
        let vn = self.heap[n as usize].to();
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
    fn insert(&mut self, vi: VarId, activity: f64) -> usize {
        if self.contains(vi) {
            return self.idxs[vi as usize] as usize;
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n as usize].to();
        self.heap.swap(i as usize, n as usize);
        self.heap[n as usize].index = activity;
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
        let vn = self.heap[n as usize].to();
        self.heap.swap(n as usize, i as usize);
        self.idxs.swap(vn as usize, vi);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            return Some(i as usize);
        }
        None
    }
}

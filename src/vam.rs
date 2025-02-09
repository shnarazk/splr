//! Variable Activity Manager with idempotent heap
#![allow(static_mut_refs)]
use {
    crate::{assign::AssignStack, config::Config, types::*, var_vector::*},
    std::fmt,
};

#[cfg(feature = "trail_saving")]
use crate::assign::TrailSavingIF;

pub struct VarActivityManager {
    activity_decay: f64,
    activity_anti_decay: f64,
    #[cfg(feature = "boundary_check")]
    tick: usize,
}

pub static mut VAM: VarActivityManager = VarActivityManager {
    activity_decay: 0.95,
    activity_anti_decay: 0.05,
    #[cfg(feature = "boundary_check")]
    tick: 0,
};

static mut VAR_HEAP: VarIdHeap = VarIdHeap {
    heap: vec![],
    idxs: vec![],
};

impl VarActivityManager {
    pub fn instantiate(config: &Config, _cnf: &CNFDescription) {
        unsafe {
            VAR_HEAP = VarIdHeap::new(VarRef::num_vars());
            VAM.activity_decay = config.vrw_dcy_rat;
            VAM.activity_anti_decay = 1.0 - config.vrw_dcy_rat;
        }
    }
    pub fn var_activity_decay_rate() -> f64 {
        unsafe { VAM.activity_decay }
    }
    pub fn set_activity_decay(decay: f64) {
        unsafe {
            VAM.activity_decay = decay;
            VAM.activity_anti_decay = 1.0 - decay;
        }
    }
    pub fn update_var_activity(vi: VarId) {
        unsafe {
            VarRef(vi).update_activity(VAM.activity_decay, VAM.activity_anti_decay);
        }
    }
    pub fn reward_at_analysis(vi: VarId) {
        VarRef(vi).turn_on(FlagVar::USED);
    }
    #[inline]
    pub fn reward_at_assign(_vi: VarId) {}
    #[inline]
    pub fn reward_at_propagation(_vi: VarId) {}
    #[inline]
    pub fn reward_at_unassign(vi: VarId) {
        unsafe {
            VarRef(vi).update_activity(VAM.activity_decay, VAM.activity_anti_decay);
        }
    }
    pub fn clear_heap() {
        unsafe {
            VAR_HEAP.clear_heap();
        }
    }
    pub fn expand_heap() {
        unsafe {
            VAR_HEAP.expand_heap();
        }
    }
    pub fn insert_heap(vi: VarId) {
        unsafe {
            VAR_HEAP.insert_heap(vi);
        }
    }
    pub fn update_heap(vi: VarId) {
        unsafe {
            VAR_HEAP.update_heap(vi);
        }
    }
    pub fn get_heap_root(asg: &mut AssignStack) -> VarId {
        unsafe { VAR_HEAP.get_heap_root(asg) }
    }
    pub fn remove_from_heap(vi: VarId) {
        unsafe {
            VAR_HEAP.remove_from_heap(vi);
        }
    }

    // pub fn add_var(vi: VarId) {
    //     unsafe {
    //         VAR_HEAP.insert_heap(vi);
    //     }
    // }
    // pub fn remove_var(vi: VarId) {
    //     unsafe {
    //         VAR_HEAP.remove_from_heap(vi);
    //     }
    // }
    // pub fn pop_top_var(asg: &mut AssignStack) -> VarId {
    //     unsafe { VAR_HEAP.get_heap_root(asg) }
    // }
    #[cfg(feature = "boundary_check")]
    pub fn update_activity_tick() {
        unsafe {
            VAM.tick += 1;
        }
    }
}

//
// Heap struct for selecting decision vars
//

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
// Decision var selection

use rustc_data_structures::fx::FxHashMap;

/// API for var selection, depending on an internal heap.
pub trait VarSelectIF {
    /// give rewards to vars selected by SLS
    fn reward_by_sls(assignment: &FxHashMap<VarId, bool>) -> usize;
    /// select a new decision variable.
    fn select_decision_literal(asg: &mut AssignStack) -> Lit;
    /// update the internal heap on var order.
    fn update_order(v: VarId);
    /// rebuild the internal var_order
    fn rebuild_order();
}

impl VarSelectIF for VarActivityManager {
    fn reward_by_sls(assignment: &FxHashMap<VarId, bool>) -> usize {
        unsafe {
            let mut num_flipped = 0;
            for (vi, b) in assignment.iter() {
                if VarRef(*vi).is(FlagVar::PHASE) != *b {
                    num_flipped += 1;
                    VarRef(*vi).set_flag(FlagVar::PHASE, *b);
                    VarRef(*vi).set_activity(
                        VarRef(*vi).activity() * VAM.activity_decay + VAM.activity_anti_decay,
                    );
                    VarActivityManager::update_heap(*vi);
                }
            }
            num_flipped
        }
    }
    fn select_decision_literal(asg: &mut AssignStack) -> Lit {
        loop {
            let vi = VarActivityManager::get_heap_root(asg); // self.get_heap_root();
            if VarRef(vi).assign().is_none() && !VarRef(vi).is(FlagVar::ELIMINATED) {
                return Lit::from((vi, VarRef(vi).is(FlagVar::PHASE)));
            }
        }
    }
    fn update_order(v: VarId) {
        VarActivityManager::update_heap(v);
    }
    fn rebuild_order() {
        VarActivityManager::clear_heap();
        for vi in VarRef::var_id_iter() {
            if VarRef(vi).assign().is_none() && !VarRef(vi).is(FlagVar::ELIMINATED) {
                VarActivityManager::insert_heap(vi);
            }
        }
    }
}

/// Internal heap manipulation API
pub trait VarHeapIF {
    fn clear_heap(&mut self);
    fn expand_heap(&mut self);
    fn insert_heap(&mut self, vi: VarId);
    fn update_heap(&mut self, v: VarId);
    fn get_heap_root(&mut self, asg: &mut AssignStack) -> VarId;
    fn percolate_up(&mut self, start: u32);
    fn percolate_down(&mut self, start: u32);
    fn remove_from_heap(&mut self, vs: VarId);
}

impl VarHeapIF for VarIdHeap {
    fn clear_heap(&mut self) {
        self.clear();
    }
    fn expand_heap(&mut self) {
        // Fill a new slot with the value that would be used in VarIdHeap::new.
        let id = self.heap.len() as u32;
        self.heap.push(id);
        self.idxs.push(id);
    }
    fn update_heap(&mut self, v: VarId) {
        debug_assert!(v != 0, "Invalid VarId");
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(start);
        }
    }
    fn insert_heap(&mut self, vi: VarId) {
        let i = self.insert(vi);
        self.percolate_up(i as u32);
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
        let vq = self.heap[q as usize];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = VarRef(vq as usize).activity();
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q as usize] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq as usize] = q;
                return;
            } else {
                let vp = self.heap[p as usize];
                let ap = VarRef(vp as usize).activity();
                if ap < aq {
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
    fn percolate_down(&mut self, start: u32) {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i as usize];
        let ai = VarRef(vi as usize).activity();
        loop {
            let l = 2 * i; // left
            if l < n as u32 {
                let vl = self.heap[l as usize];
                let al = VarRef(vl as usize).activity();
                let r = l + 1; // right
                let (target, vc, ac) =
                    if r < (n as u32) && al < VarRef(self.heap[r as usize] as usize).activity() {
                        let vr = self.heap[r as usize];
                        (r, vr, VarRef(vr as usize).activity())
                    } else {
                        (l, vl, al)
                    };
                if ai < ac {
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

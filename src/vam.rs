#![allow(static_mut_refs)]
use {
    crate::{types::*, var_vector::*},
    std::collections::BinaryHeap,
};

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

static mut VAR_HEAP: BinaryHeap<OrderedProxy<VarId>> = BinaryHeap::new();

impl VarActivityManager {
    pub fn initialize() {
        unsafe {
            VAR_HEAP.clear();
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
    pub fn add_var(vi: VarId) {
        unsafe {
            VAR_HEAP.push(OrderedProxy::new(vi, VarRef(vi).activity()));
        }
    }
    pub fn remove_var(vi: VarId) {
        unsafe {
            VAR_HEAP.retain(|x| x.to() != vi);
        }
    }
    pub fn pop_top_var() -> Option<VarId> {
        unsafe {
            if let Some(op) = VAR_HEAP.pop() {
                Some(op.to())
            } else {
                None
            }
        }
    }
    pub fn increment_tick() {
        unsafe {
            VAM.tick += 1;
        }
    }
}

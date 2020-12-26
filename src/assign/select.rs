#[cfg(feature = "temp_order")]
use std::collections::BinaryHeap;
/// Decision var selection
use {
    super::{AssignStack, Var, VarHeapIF, VarOrderIF, VarRewardIF},
    crate::{state::RephaseMode, types::*},
};

#[cfg(feature = "temp_order")]
use std::slice::Iter;

/// ```
/// let x: Lbool = var_assign!(self, lit.vi());
/// ```
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
    };
}

/// API for var selection, depending on an internal heap.
pub trait VarSelectIF {
    #[cfg(feature = "temp_order")]
    /// force assignments
    fn force_select_iter(&mut self, iterator: Option<Iter<'_, usize>>);
    /// force assignments
    fn force_rephase(&mut self, phase: RephaseMode);
    /// select a new decision variable.
    fn select_decision_literal(&mut self, select_best: bool) -> Lit;
    /// save the current assignments to BEST_PHASE
    fn save_phases(&mut self);
    /// update the internal heap on var order.
    fn update_order(&mut self, v: VarId);
    /// rebuild the internal var_order
    fn rebuild_order(&mut self);
    /// make a var asserted.
    fn make_var_asserted(&mut self, vi: VarId);
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
struct VarTimestamp {
    timestamp: usize,
    vi: VarId,
}

impl From<&Var> for VarTimestamp {
    fn from(v: &Var) -> Self {
        VarTimestamp {
            timestamp: v.timestamp,
            vi: v.index,
        }
    }
}

impl VarSelectIF for AssignStack {
    #[cfg(feature = "temp_order")]
    #[allow(unused_variables)]
    fn force_select_iter(&mut self, iterator: Option<Iter<'_, usize>>) {
        {
            if let Some(iter) = iterator {
                for vi in iter.rev() {
                    let lit = Lit::from_assign(*vi, self.var[*vi].is(Flag::PHASE));
                    self.temp_order.push(lit);
                }
            } else {
                let mut heap: BinaryHeap<VarTimestamp> = BinaryHeap::new();
                let remains = self.num_vars - self.num_asserted_vars - self.num_eliminated_vars;
                let size = (remains as f64).sqrt() as usize; //remains.count_ones() as usize;
                for v in self.var.iter().skip(1) {
                    if self.assign[v.index].is_some() {
                        continue;
                    }
                    if let Some(top) = heap.peek() {
                        if v.timestamp < top.timestamp {
                            heap.push(VarTimestamp::from(v));
                            if size < heap.len() {
                                heap.pop();
                            }
                        }
                    }
                }
                for v in heap.iter() {
                    let lit = Lit::from_assign(v.vi, self.var[v.vi].is(Flag::PHASE));
                    self.temp_order.push(lit);
                }
            }
        }
    }
    fn force_rephase(&mut self, phase: RephaseMode) {
        debug_assert!(self.use_rephase);
        #[cfg(feature = "temp_order")]
        {
            self.temp_order.clear();
        }
        self.best_phase_reward_value = self.best_phase_reward_value.sqrt();
        match phase {
            RephaseMode::Best => {
                for vi in self.var_order.heap[1..].iter().rev() {
                    let v = &mut self.var[*vi];
                    if v.is(Flag::REPHASE) {
                        #[cfg(not(feature = "temp_order"))]
                        {
                            v.best_phase_reward = self.best_phase_reward_value;
                        }
                        #[cfg(feature = "temp_order")]
                        {
                            self.temp_order
                                .push(Lit::from_assign(v, v.is(Flag::BEST_PHASE)));
                        }
                    } else {
                        #[cfg(not(feature = "temp_order"))]
                        {
                            v.best_phase_reward = 0.0;
                        }
                    }
                }
            }
            RephaseMode::Clear => (),
            #[cfg(feature = "explore_timestamp")]
            #[cfg(feature = "temp_order")]
            RephaseMode::Explore(since) => {
                for vi in self.var_order.heap[1..].iter() {
                    let v = &mut self.var[*vi];
                    if v.assign_timestamp < since {
                        self.temp_order
                            .push(Lit::from_assign(*vi, v.timestamp % 2 == 0));
                    }
                }
            }
            #[cfg(feature = "temp_order")]
            RephaseMode::Force(on) => {
                for vi in self.var_order.heap[1..].iter().rev() {
                    self.temp_order.push(Lit::from_assign(*vi, on));
                }
            }
            #[cfg(feature = "temp_order")]
            RephaseMode::Random => {
                let limit = 10000;
                let len = self.var_order.idxs[0].min(limit);
                for vi in self.var_order.heap[1..].iter().rev() {
                    let b = self.var[*vi].timestamp % 2 == 0;
                    self.temp_order.push(Lit::from_assign(*vi, b));
                }
            }
        }
    }
    fn select_decision_literal(&mut self, select_best: bool) -> Lit {
        #[cfg(feature = "temp_order")]
        {
            while let Some(lit) = self.temp_order.pop() {
                if self.assign[lit.vi()].is_none() && !self.var[lit.vi()].is(Flag::ELIMINATED) {
                    return lit;
                }
            }
        }
        let vi = self.select_var();
        let p = self.var[vi].is(if select_best && self.var[vi].is(Flag::REPHASE) {
            Flag::BEST_PHASE
        } else {
            Flag::PHASE
        });
        Lit::from_assign(vi, p)
    }
    fn save_phases(&mut self) {
        for (vi, v) in self.var.iter_mut().enumerate().skip(1) {
            if !v.is(Flag::ELIMINATED) {
                if let Some(b) = self.assign[vi] {
                    v.turn_on(Flag::REPHASE);
                    v.set(Flag::BEST_PHASE, b);
                    v.best_phase_reward = self.best_phase_reward_value;
                    continue;
                }
                v.turn_off(Flag::REPHASE);
                v.best_phase_reward = 0.0;
            }
        }
        self.build_best_at = self.num_propagation;
    }
    fn update_order(&mut self, v: VarId) {
        self.update_heap(v);
    }
    fn rebuild_order(&mut self) {
        self.var_order.clear();
        for vi in 1..self.var.len() {
            if var_assign!(self, vi).is_none() && !self.var[vi].is(Flag::ELIMINATED) {
                self.insert_heap(vi);
            }
        }
    }
    fn make_var_asserted(&mut self, vi: VarId) {
        self.num_asserted_vars += 1;
        self.clear_reward(vi);
        self.remove_from_heap(vi);
        self.check_best_phase(vi);
    }
}

impl AssignStack {
    fn select_var(&mut self) -> VarId {
        loop {
            let vi = self.get_heap_root();
            if var_assign!(self, vi).is_none() && !self.var[vi].is(Flag::ELIMINATED) {
                return vi;
            }
        }
    }
    /// check usability of the saved best phase
    fn check_best_phase(&mut self, vi: VarId) -> bool {
        if self.var[vi].is(Flag::ELIMINATED) {
            return false;
        }
        if self.level[vi] == self.root_level && self.var[vi].is(Flag::REPHASE) {
            if let Some(phase) = self.assign[vi] {
                if phase != self.var[vi].is(Flag::BEST_PHASE) {
                    self.num_best_assign = 0;
                    self.var[vi].best_phase_reward = 0.0;
                    return true;
                }
            }
        }
        false
    }
}

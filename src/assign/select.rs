#[cfg(feature = "temp_order")]
use std::collections::BinaryHeap;
/// Decision var selection
use {
    super::{AssignStack, Var, VarHeapIF, VarOrderIF},
    crate::{state::RephaseMode, types::*},
    std::slice::Iter,
};

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
    /// force assignments
    fn force_select_iter(&mut self, iterator: Option<Iter<'_, usize>>);
    /// force assignments
    fn force_rephase(&mut self, phase: &RephaseMode);
    /// select a new decision variable.
    fn select_decision_literal(&mut self) -> Lit;
    /// save the current assignments to BEST_PHASE.
    fn save_phases(&mut self);
    /// update the internal heap on var order.
    fn update_order(&mut self, v: VarId);
    /// rebuild the internal var_order
    fn rebuild_order(&mut self);
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
    #[allow(unused_variables)]
    fn force_select_iter(&mut self, iterator: Option<Iter<'_, usize>>) {
        #[cfg(feature = "temp_order")]
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
    fn force_rephase(&mut self, phase: &RephaseMode) {
        if !self.use_rephase {
            return;
        }
        let range = 1..(self.num_conflict / self.num_restart).min(self.var_order.len());
        match phase {
            RephaseMode::Best => {
                for vi in range {
                    let v = &mut self.var[vi];
                    if v.is(Flag::REPHASE) {
                        v.set(Flag::PHASE, v.is(Flag::BEST_PHASE));
                    }
                }
            }
            RephaseMode::Force(on) => {
                for vi in range {
                    self.var[vi].set(Flag::PHASE, *on);
                }
            }
            RephaseMode::Invert => {
                for vi in range {
                    let b = !self.var[vi].is(Flag::PHASE);
                    self.var[vi].set(Flag::PHASE, b);
                }
            }
            RephaseMode::Random => {
                for vi in range {
                    let b = self.var[vi].timestamp % 2 == 0;
                    self.var[vi].set(Flag::PHASE, b);
                }
            }
        }
    }
    fn select_decision_literal(&mut self) -> Lit {
        #[cfg(feature = "temp_order")]
        {
            while let Some(lit) = self.temp_order.pop() {
                if self.assign[lit.vi()].is_none() && !self.var[lit.vi()].is(Flag::ELIMINATED) {
                    return lit;
                }
            }
        }
        let vi = self.select_var();
        let p = self.var[vi].is(Flag::PHASE);
        Lit::from_assign(vi, p)
    }
    fn save_phases(&mut self) {
        for (vi, v) in self.var.iter_mut().enumerate().skip(1) {
            if !v.is(Flag::ELIMINATED) {
                if let Some(b) = self.assign[vi] {
                    v.turn_on(Flag::REPHASE);
                    v.set(Flag::BEST_PHASE, b);
                    continue;
                }
                v.turn_off(Flag::REPHASE);
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
}

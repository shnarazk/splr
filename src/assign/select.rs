// Decision var selection

#[cfg(feature = "rephase")]
use super::property;

use {
    super::{heap::VarHeapIF, stack::AssignStack},
    crate::types::*,
};

/// ```ignore
/// let x: Option<bool> = var_assign!(self, lit.vi());
/// ```
#[cfg(feature = "unsafe_access")]
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { $asg.var.get_unchecked($var).assign }
    };
}
#[cfg(not(feature = "unsafe_access"))]
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        $asg.assign[$var]
    };
}

/// API for var selection, depending on an internal heap.
pub trait VarSelectIF {
    /// return a new vector to store phases.
    fn new_phases_store(&self) -> Vec<Option<bool>>;
    /// copy the current best phases to `phases`.
    fn save_best_phases(&self, phases: &mut [bool]);
    /// copy the current assignments to `phases`.
    fn save_current_phases(&self, phases: &mut [bool]);
    /// set `VarFlag::PHASE`s from `phases`.
    fn load_phases(&mut self, phases: &[bool], flip: bool);
    /// randomize `VarFlag::PHASE`s.
    fn randomize_phases(&mut self);
    /// select rephasing target
    fn select_rephasing_target(&mut self);
    /// check the consistency
    fn check_consistency_of_best_phases(&mut self);
    /// select a new decision variable.
    fn select_decision_literal(&mut self) -> Lit;
    /// update the internal heap on var order.
    fn update_order(&mut self, v: VarId);
    /// rebuild the internal var_order
    fn rebuild_order(&mut self);
}

impl VarSelectIF for AssignStack {
    fn new_phases_store(&self) -> Vec<Option<bool>> {
        vec![None; self.num_vars + 1]
    }
    fn save_best_phases(&self, phases: &mut [bool]) {
        for (i, (a, _)) in self.best_phases.iter() {
            phases[*i] = *a;
        }
    }
    fn save_current_phases(&self, phases: &mut [bool]) {
        for (i, v) in self.var.iter().enumerate().skip(1) {
            phases[i] = v.assign.unwrap_or_default();
        }
    }
    fn load_phases(&mut self, phases: &[bool], flip: bool) {
        for (i, v) in self.var.iter_mut().enumerate().skip(1) {
            if !v.is(FlagVar::ELIMINATED) && v.reason != AssignReason::Decision(0) {
                v.assign = Some(phases[i] ^ flip);
            }
        }
    }
    fn randomize_phases(&mut self) {
        let mut seed = self.num_vars + self.num_conflict;
        seed = seed.saturating_mul(seed);
        for (i, v) in self.var.iter_mut().enumerate().skip(1) {
            if v.is(FlagVar::ELIMINATED) || v.reason == AssignReason::Decision(0) {
                seed = seed.saturating_mul(7);
            } else {
                seed = seed.saturating_add(i + v.level as usize);
                seed = seed.rotate_left(13);
                v.assign = Some(seed.is_multiple_of(2));
            }
        }
    }
    fn select_rephasing_target(&mut self) {
        if self.best_phases.is_empty() {
            return;
        }
        self.check_consistency_of_best_phases();
        if self.derefer(property::Tusize::NumUnassertedVar) <= self.best_phases.len() {
            self.best_phases.clear();
            return;
        }
        debug_assert!(
            self.best_phases
                .iter()
                .all(|(vi, b)| self.var[*vi].assign != Some(!b.0))
        );
        self.num_rephase += 1;
        for (vi, (b, _)) in self.best_phases.iter() {
            let v = &mut self.var[*vi];
            v.set(FlagVar::PHASE, *b);
        }
    }
    fn check_consistency_of_best_phases(&mut self) {
        if self
            .best_phases
            .iter()
            .any(|(vi, b)| self.var[*vi].assign == Some(!b.0))
        {
            self.best_phases.clear();
            self.num_best_assign = self.num_asserted_vars + self.num_eliminated_vars;
        }
    }
    fn select_decision_literal(&mut self) -> Lit {
        let vi = self.select_var();
        Lit::from((vi, self.var[vi].is(FlagVar::PHASE)))
    }
    fn update_order(&mut self, v: VarId) {
        self.update_heap(v);
    }
    fn rebuild_order(&mut self) {
        self.clear_heap();
        for vi in 1..self.var.len() {
            if var_assign!(self, vi).is_none() && !self.var[vi].is(FlagVar::ELIMINATED) {
                self.insert_heap(vi);
            }
        }
    }
}

impl AssignStack {
    /// select a decision var
    fn select_var(&mut self) -> VarId {
        loop {
            let vi = self.get_heap_root();
            if var_assign!(self, vi).is_none() && !self.var[vi].is(FlagVar::ELIMINATED) {
                return vi;
            }
        }
    }
}

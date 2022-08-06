/// Decision var selection

#[cfg(feature = "rephase")]
use super::property;

use {
    super::{AssignStack, VarHeapIF},
    crate::types::*,
};

/// ```ignore
/// let x: Option<bool> = var_assign!(self, lit.vi());
/// ```
#[cfg(feature = "unsafe_access")]
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
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
    #[cfg(feature = "rephase")]
    /// select rephasing target
    fn select_rephasing_target(&mut self);
    #[cfg(feature = "rephase")]
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
    #[cfg(feature = "rephase")]
    fn select_rephasing_target(&mut self) {
        if self.best_phases.is_empty() {
            return;
        }
        self.check_consistency_of_best_phases();
        if self.derefer(property::Tusize::NumUnassertedVar) <= self.best_phases.len() {
            self.best_phases.clear();
            return;
        }
        debug_assert!(self
            .best_phases
            .iter()
            .all(|(vi, b)| self.assign[*vi] != Some(!b.0)));
        self.num_rephase += 1;
        for (vi, (b, _)) in self.best_phases.iter() {
            let v = &mut self.var[*vi];
            v.set(FlagVar::PHASE, *b);
        }
    }
    #[cfg(feature = "rephase")]
    fn check_consistency_of_best_phases(&mut self) {
        if self
            .best_phases
            .iter()
            .any(|(vi, b)| self.assign[*vi] == Some(!b.0))
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

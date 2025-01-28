// Decision var selection

#[cfg(feature = "rephase")]
use super::property;

use {
    super::{heap::VarHeapIF, stack::AssignStack},
    crate::types::*,
    std::collections::HashMap,
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
    #[cfg(feature = "rephase")]
    /// return best phases
    fn best_phases_ref(&mut self, default_value: Option<bool>) -> HashMap<VarId, bool>;
    #[cfg(feature = "rephase")]
    /// force an assignment obtained by SLS
    fn override_rephasing_target(&mut self, assignment: &HashMap<VarId, bool>) -> usize;
    /// give rewards to vars selected by SLS
    fn reward_by_sls(&mut self, assignment: &HashMap<VarId, bool>) -> usize;
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
    fn best_phases_ref(&mut self, default_value: Option<bool>) -> HashMap<VarId, bool> {
        self.var
            .iter()
            .enumerate()
            .filter_map(|(vi, v)| {
                if v.level == self.root_level || v.is(FlagVar::ELIMINATED) {
                    default_value.map(|b| (vi, b))
                } else {
                    Some((
                        vi,
                        self.best_phases.get(&vi).map_or(
                            self.var[vi].assign.unwrap_or_else(|| v.is(FlagVar::PHASE)),
                            |(b, _)| *b,
                        ),
                    ))
                }
            })
            .collect::<HashMap<VarId, bool>>()
    }
    #[cfg(feature = "rephase")]
    fn override_rephasing_target(&mut self, assignment: &HashMap<VarId, bool>) -> usize {
        let mut num_flipped = 0;
        for (vi, b) in assignment.iter() {
            if self.best_phases.get(vi).is_none_or(|(p, _)| *p != *b) {
                num_flipped += 1;
                self.best_phases.insert(*vi, (*b, AssignReason::None));
            }
        }
        num_flipped
    }
    fn reward_by_sls(&mut self, assignment: &HashMap<VarId, bool>) -> usize {
        let mut num_flipped = 0;
        for (vi, b) in assignment.iter() {
            let v = &mut self.var[*vi];
            if v.is(FlagVar::PHASE) != *b {
                num_flipped += 1;
                v.set(FlagVar::PHASE, *b);
                v.reward *= self.activity_decay;
                v.reward += self.activity_anti_decay;
                self.update_heap(*vi);
            }
        }
        num_flipped
    }
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
            .all(|(vi, b)| self.var[*vi].assign != Some(!b.0)));
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

//! Decision var selection

use {
    super::{AssignIF, heap::VarHeapIF, stack::AssignStack},
    crate::types::*,
};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum PhaseRotation {
    #[default]
    Walk,
    Best,
    False,
    True,
    Random,
    Inverted,
}

impl PhaseRotation {
    /// return a symbolic (Unicode) letter for each value of `PhaseRotation`.
    pub fn as_mnemonic(&self) -> &str {
        match self {
            PhaseRotation::Walk => "→",
            PhaseRotation::Best => "★",
            PhaseRotation::False => "⊥",
            PhaseRotation::True => "⊤",
            PhaseRotation::Random => "∼",
            PhaseRotation::Inverted => "¬",
        }
    }
}

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
    fn check_consistency_of_best_phases(&mut self);
    /// select a new decision variable.
    fn select_decision_literal(&mut self) -> Lit;
    /// update the internal heap on var order.
    fn update_order(&mut self, v: VarId);
    /// rebuild the internal var_order
    fn rebuild_order(&mut self);
    /// save the current assignments as the best phases
    fn save_best_phases(&mut self);
}

impl VarSelectIF for AssignStack {
    fn check_consistency_of_best_phases(&mut self) {
        if self
            .best_phases
            .iter()
            .any(|(vi, b)| self.var[*vi].assign == Some(!b.0))
        {
            self.best_phases.clear();
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
    fn save_best_phases(&mut self) {
        self.best_phases.clear();
        for l in self.trail.iter().skip(self.len_upto(self.root_level)) {
            let vi = l.vi();
            if let Some(b) = self.var[vi].assign {
                self.best_phases.insert(vi, (b, self.var[vi].reason));
                self.var[vi].best_level = self.var[vi].level;
            } else {
                self.var[vi].best_level = u32::MAX;
            }
        }
        // self.build_best_at = self.num_propagation;
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

//! Decision var selection

use {
    super::{heap::VarHeapIF, stack::AssignStack},
    crate::types::*,
};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum RephaseTarget {
    #[default]
    Walk,
    Best,
    False,
    True,
    Random,
    Inverted,
    Polarity,
}

impl RephaseTarget {
    /// return a symbolic (Unicode) letter for each value of `PhaseRotation`.
    pub fn as_mnemonic(&self) -> &str {
        match self {
            RephaseTarget::Walk => "→",
            RephaseTarget::Best => "★",
            RephaseTarget::False => "⊥",
            RephaseTarget::True => "⊤",
            RephaseTarget::Random => "∼",
            RephaseTarget::Inverted => "¬",
            RephaseTarget::Polarity => "φ",
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
        $asg.var[$var].assign
    };
}

/// API for var selection, depending on an internal heap.
pub trait VarSelectIF {
    /// return `None` if current assignment is not compatible with the values.
    /// Othewise return `Some(the core size)`.
    fn check_best_phases(&mut self) -> Option<usize>;
    /// select a new decision variable.
    fn select_decision_literal(&mut self) -> Lit;
    /// update the internal heap on var order.
    fn update_order(&mut self, v: VarId);
    /// rebuild the internal var_order
    fn rebuild_order(&mut self);
    /// save the current assignments as the best phases.
    /// return the core size.
    fn save_best_phases(&mut self, new_best: bool) -> usize;
    fn clear_best_phases(&mut self);
}

impl VarSelectIF for AssignStack {
    fn check_best_phases(&mut self) -> Option<usize> {
        let mut alives = 0;
        let mut inconsistent: bool = false;
        for (vi, b) in self.best_phases.iter_mut().enumerate().skip(1) {
            match (b.0, self.var[vi].assign) {
                (Some(_), None) if !self.var[vi].is(FlagVar::ELIMINATED) => {
                    alives += 1;
                }
                (Some(bp), Some(a)) if bp == a => {
                    *b = (None, DecisionLevel::MAX);
                }
                (Some(_), Some(_)) => {
                    inconsistent = true;
                    break;
                }
                _ => (),
            }
        }
        if inconsistent {
            self.best_phases.fill((None, DecisionLevel::default()));
            None
        } else {
            Some(self.num_vars - alives - self.num_asserted_vars - self.num_eliminated_vars)
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
    fn save_best_phases(&mut self, new_best: bool) -> usize {
        let mut alives: usize = 0;
        for (vi, v) in self.var.iter_mut().enumerate().skip(1) {
            if let Some(b) = v.assign
                && v.level > self.root_level
                && !v.is(FlagVar::ELIMINATED)
            {
                if new_best {
                    self.best_phases[vi] = (Some(b), v.level);
                }
                alives += 1;
            } else {
                if new_best {
                    self.best_phases[vi] = (None, DecisionLevel::MAX);
                }
            }
        }
        self.num_vars - alives - self.num_asserted_vars - self.num_eliminated_vars
    }
    fn clear_best_phases(&mut self) {
        for (vi, v) in self.var.iter_mut().enumerate().skip(1) {
            if v.level > self.root_level && !v.is(FlagVar::ELIMINATED) {
                self.best_phases[vi] = (None, DecisionLevel::MAX);
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

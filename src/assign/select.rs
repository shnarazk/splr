/// Decision var selection

#[cfg(feature = "rephase")]
use super::property;

use {
    super::{AssignStack, Var, VarHeapIF},
    crate::types::*,
};

/// ```
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
    fn select_rephasing_target(&mut self, request: Option<RephasingTarget>, span: usize);
    /// select a new decision variable.
    fn select_decision_literal(&mut self) -> Lit;
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

/// Phase saving modes.
#[cfg(feature = "rephase")]
#[derive(Debug, Eq, PartialEq)]
pub enum RephasingTarget {
    ///
    AllTrue,
    /// use best phases
    BestPhases,
    /// unstage all vars.
    Clear,
    ///
    Inverted,
    /// a kind of random shuffle
    Shift,
    ///
    XorShift,
}

#[cfg(feature = "rephase")]
impl std::fmt::Display for RephasingTarget {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "{:?}", self)
    }
}

impl VarSelectIF for AssignStack {
    #[cfg(feature = "rephase")]
    fn select_rephasing_target(&mut self, request: Option<RephasingTarget>, level: usize) {
        if self.best_phases.is_empty() {
            return;
        }
        if self.derefer(property::Tusize::NumUnassertedVar) <= self.best_phases.len() {
            self.best_phases.clear();
            return;
        }
        let remain = self.derefer(property::Tusize::NumUnassertedVar) - self.best_phases.len() + 1;
        if (remain as f64).log10() < level as f64 {
            return;
        }
        let target = if let Some(t) = request {
            t
        } else {
            self.phase_age += 1;
            match self.phase_age {
                0 | 1 | 6 => RephasingTarget::Clear,
                2 | 3 | 5 => RephasingTarget::BestPhases,
                4 | 7 => RephasingTarget::Inverted,
                x if x % 8 == 2 => RephasingTarget::BestPhases,
                x if x % 8 == 6 => RephasingTarget::Inverted,
                _ => RephasingTarget::Clear,
            }
        };
        let mut s = true;
        // The iteration order by an iterator on HashMap may change in each execution.
        // So Shift and XorShift cause non-determinism. Be careful.
        let mut invalidated = false;
        for (vi, (b, _)) in self.best_phases.iter() {
            let v = &mut self.var[*vi];
            if self.assign[*vi] == Some(!*b) {
                invalidated = true;
            }
            match target {
                RephasingTarget::AllTrue => v.set(Flag::PHASE, true),
                // RephasingTarget::BestPhases => v.set(Flag::PHASE, *b),
                // RephasingTarget::Inverted => v.set(Flag::PHASE, !*b),
                RephasingTarget::Inverted => v.set(Flag::PHASE, false),
                RephasingTarget::Shift => {
                    v.set(Flag::PHASE, s);
                    // s = *b;
                }
                RephasingTarget::XorShift => {
                    v.set(Flag::PHASE, s);
                    // s ^= *b;
                }
                RephasingTarget::Clear => (),
                _ => (),
            }
        }
        if invalidated {
            self.best_phases.clear();
            self.num_best_assign = self.num_eliminated_vars;
        } else {
            self.num_rephase += 1;
        }
    }
    fn select_decision_literal(&mut self) -> Lit {
        let vi = self.select_var();
        Lit::from_assign(vi, self.var[vi].is(Flag::PHASE))
    }
    fn update_order(&mut self, v: VarId) {
        self.update_heap(v);
    }
    fn rebuild_order(&mut self) {
        self.clear_heap();
        for vi in 1..self.var.len() {
            if var_assign!(self, vi).is_none() && !self.var[vi].is(Flag::ELIMINATED) {
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
            if var_assign!(self, vi).is_none() && !self.var[vi].is(Flag::ELIMINATED) {
                return vi;
            }
        }
    }
}

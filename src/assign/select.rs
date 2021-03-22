/// Decision var selection

#[cfg(feature = "rephase")]
use {super::property, crate::state::RephasingTarget};

use {
    super::{AssignStack, Var, VarHeapIF},
    crate::types::*,
};

/// ```
/// let x: Option<bool> = var_assign!(self, lit.vi());
/// ```
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
    };
}

/// API for var selection, depending on an internal heap.
pub trait VarSelectIF {
    #[cfg(feature = "rephase")]
    /// select rephasing target
    fn select_rephasing_target(&mut self, request: Option<RephasingTarget>, span: usize);
    /// return the number of forgotton vars.
    fn num_ion(&self) -> (usize, usize);

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

impl VarSelectIF for AssignStack {
    #[cfg(not(feature = "best_phases_tracking"))]
    fn num_ion(&self) -> (usize, usize) {
        (0, 0)
    }
    #[cfg(feature = "best_phases_tracking")]
    fn num_ion(&self) -> (usize, usize) {
        let thr = self.average_activity();
        let mut num_negative = 0; // unreachable core side
        let mut num_positive = 0; // decision var side

        for v in self.var.iter().skip(1) {
            if !v.is(Flag::ELIMINATED)
                && thr < v.activity()
                && self.root_level < self.level[v.index]
            {
                match self.best_phases.get(&v.index) {
                    Some((_, AssignReason::Implication(_, NULL_LIT))) => {
                        num_positive += 1;
                    }
                    None => {
                        num_negative += 1;
                    }
                    _ => (),
                }
            }
        }
        (num_negative, num_positive)
    }
    #[cfg(feature = "rephase")]
    fn select_rephasing_target(&mut self, request: Option<RephasingTarget>, span: usize) {
        if self.best_phases.is_empty() {
            return;
        }
        if self.derefer(property::Tusize::NumUnassertedVar) <= self.best_phases.len() {
            self.best_phases.clear();
            return;
        }
        let remain = self.derefer(property::Tusize::NumUnassertedVar) - self.best_phases.len() + 1;
        if (remain as f64).log10() < span as f64 {
            return;
        }
        let target = if let Some(t) = request {
            t
        } else {
            self.stage_mode_select += 1;
            match self.stage_mode_select % 3 {
                1 => RephasingTarget::Inverted,
                2 => RephasingTarget::BestPhases,
                _ => RephasingTarget::Clear,
            }
        };
        match target {
            RephasingTarget::BestPhases => {
                for (vi, (b, _)) in self.best_phases.iter() {
                    let v = &mut self.var[*vi];
                    v.set(Flag::PHASE, *b);
                }
                self.num_rephase += 1;
            }
            RephasingTarget::Inverted => {
                for (vi, (b, _)) in self.best_phases.iter() {
                    let v = &mut self.var[*vi];
                    v.set(Flag::PHASE, !*b);
                }
                self.num_rephase += 1;
            }
            RephasingTarget::Clear => (),
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

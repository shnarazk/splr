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
#[derive(Debug, PartialEq)]
pub enum RephasingTarget {
    /// use best phases
    BestPhases,
    /// unstage all vars.
    Clear,
    /// a kind of random shuffle
    Shift(f64),
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
                0 | 2 | 4 => RephasingTarget::BestPhases,
                1 => RephasingTarget::Shift(0.5),
                3 => RephasingTarget::Shift(0.75),
                // x if x % 4 == 1 => RephasingTarget::Clear,
                // x if x % 4 == 3 => RephasingTarget::BestPhase,
                x if x % 3 == 1 => RephasingTarget::Clear,
                // x if x % 3 == 2 => RephasingTarget::BestPhase,
                _ => RephasingTarget::Shift(0.25),
            }
        };
        // The iteration order by an iterator on HashMap may change in each execution.
        // So Shift and XorShift cause non-determinism. Be careful.
        let mut invalidated = false;
        let mut num_flip = 0;
        let mut act_sum = 0.0;
        for (vi, (b, _)) in self.best_phases.iter() {
            let v = &mut self.var[*vi];
            if self.assign[*vi] == Some(!*b) {
                invalidated = true;
            }
            match target {
                RephasingTarget::BestPhases => v.set(Flag::PHASE, *b),
                RephasingTarget::Shift(scale) => {
                    // let mut count = 0;
                    // count += *b as usize;
                    // count += s as usize;
                    // count += v.is(Flag::PHASE) as usize;
                    // s = 1 < count;
                    // // s ^= v.is(Flag::PHASE);
                    // // if v.is(Flag::PHASE) != s {
                    // //     num_match += 1;
                    // // }
                    // // v.set(Flag::PHASE, s);
                    if !v.reward.is_nan() {
                        act_sum += scale * (1.0 - v.reward);
                    }
                    if 1.0 <= act_sum {
                        v.set(Flag::PHASE, !*b);
                        act_sum = 0.0;
                        num_flip += 1;
                    } else {
                        v.set(Flag::PHASE, *b);
                    }
                }
                RephasingTarget::Clear => (),
            }
        }
        if let RephasingTarget::Shift(_) = target {
            self.bp_divergence_ema
                .update(num_flip as f64 / self.best_phases.iter().count() as f64);
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
        Lit::from((vi, self.var[vi].is(Flag::PHASE)))
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

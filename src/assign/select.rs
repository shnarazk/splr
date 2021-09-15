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
    fn select_rephasing_target(&mut self, request: Option<RephasingTarget>);
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

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
struct VarTimestamp {
    timestamp: usize,
    vi: VarId,
}

impl From<&Var> for VarTimestamp {
    fn from(v: &Var) -> Self {
        VarTimestamp {
            timestamp: v.timestamp,
            vi: v.index as usize,
        }
    }
}

/// Phase saving modes.
#[cfg(feature = "rephase")]
#[derive(Debug, PartialEq)]
pub enum RephasingTarget {
    /// use a modified best phases
    AntiPhases,
    /// use best phases
    BestPhases,
    /// unstage all vars.
    Clear,
    /// reverse phases.
    FlipAll,
    /// use the reverse of best phase
    FlipBestPhase,
    /// a kind of random shuffle
    Mixin(f64),
}

#[cfg(feature = "rephase")]
impl std::fmt::Display for RephasingTarget {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "{:?}", self)
    }
}

impl VarSelectIF for AssignStack {
    #[cfg(feature = "rephase")]
    fn select_rephasing_target(&mut self, request: Option<RephasingTarget>) {
        if self.best_phases.is_empty() {
            return;
        }
        if self.derefer(property::Tusize::NumUnassertedVar) <= self.best_phases.len() {
            self.best_phases.clear();
            return;
        }
        self.phase_age += 1;
        // let target = request.unwrap_or_else(|| RephasingTarget::Mixin(1.0 / scale as f64));
        let target = request.unwrap_or(RephasingTarget::BestPhases);
        // The iteration order by an iterator on HashMap may change in each execution.
        // So Shift and XorShift cause non-determinism. Be careful.
        let mut num_flip = 0;
        let mut act_sum = 0.0;
        debug_assert!(self
            .best_phases
            .iter()
            .all(|(vi, b)| self.assign[*vi] != Some(!b.0)));
        self.num_rephase += 1;
        match target {
            RephasingTarget::AntiPhases => {
                for (vi, (b, _)) in self.best_phases.iter() {
                    let v = &mut self.var[*vi];
                    v.set(Flag::PHASE, !*b);
                }
                /* for vi in 1..self.num_vars {
                    if !self.best_phases.contains_key(&vi) && !self.var[vi].is(Flag::ELIMINATED) {
                        self.var[vi].toggle(Flag::PHASE);
                    }
                } */
            }
            RephasingTarget::BestPhases => {
                for (vi, (b, _)) in self.best_phases.iter() {
                    let v = &mut self.var[*vi];
                    v.set(Flag::PHASE, *b);
                }
            }
            RephasingTarget::Clear => (),
            RephasingTarget::FlipAll => {
                for vi in 1..self.num_vars {
                    if !self.var[vi].is(Flag::ELIMINATED) {
                        self.var[vi].toggle(Flag::PHASE);
                    }
                }
            }
            RephasingTarget::FlipBestPhase => {
                for (vi, _) in self.best_phases.iter() {
                    let v = &mut self.var[*vi];
                    v.set(Flag::PHASE, /* !*b */ self.phase_age % 2 == 0);
                }
            }
            RephasingTarget::Mixin(scl) => {
                for (vi, (b, _)) in self.best_phases.iter() {
                    let v = &mut self.var[*vi];
                    if !v.reward.is_nan() {
                        act_sum += scl * v.reward;
                    }
                    if 1.0 <= act_sum {
                        // v.set(Flag::PHASE, !*b); NO: use the current phase!
                        act_sum = 0.0;
                        num_flip += 1;
                    } else {
                        v.set(Flag::PHASE, *b);
                    }
                }
                self.bp_divergence_ema
                    .update(num_flip as f64 / self.best_phases.len() as f64);
            }
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

#[cfg(feature = "var_staging")]
use crate::state::StagingTarget;
/// Decision var selection
use {
    super::{AssignStack, Var, VarHeapIF, VarOrderIF},
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
    // #[cfg(feature = "var_staging")]
    // /// decay staging setting
    // fn dissolve_staged_vars(&mut self, phasing: bool);

    #[cfg(feature = "var_staging")]
    /// select staged vars
    fn select_staged_vars(&mut self, request: Option<StagingTarget>, rephasing: bool);

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
                && thr < v.activity(self.stage_activity)
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
    #[cfg(feature = "var_staging")]
    fn select_staged_vars(&mut self, request: Option<StagingTarget>, rephasing: bool) {
        self.rephasing = rephasing;
        self.stage_mode_select += 1;
        let target = request.unwrap_or(StagingTarget::Clear);
        for vi in self.staged_vars.keys() {
            self.var[*vi].turn_off(Flag::STAGED);
        }
        self.staged_vars.clear();
        self.stage_activity = self.staging_reward_value;
        match target {
            StagingTarget::Backbone => {
                for (vi, (b, r)) in self.best_phases.iter() {
                    if matches!(r, AssignReason::None) {
                        let v = &mut self.var[*vi];
                        v.turn_on(Flag::STAGED);
                        v.set(Flag::PHASE, *b);
                        self.staged_vars.insert(*vi, *b);
                    }
                }
            }
            StagingTarget::BestPhases => {
                for (vi, (b, _)) in self.best_phases.iter() {
                    let v = &mut self.var[*vi];
                    v.turn_on(Flag::STAGED);
                    v.set(Flag::PHASE, *b);
                    self.staged_vars.insert(*vi, *b);
                }
            }
            StagingTarget::Clear => (),
        }
    }
    fn select_decision_literal(&mut self) -> Lit {
        let vi = self.select_var();
        #[cfg(feature = "best_phases_reuse")]
        if self.rephasing {
            if let Some((b, AssignReason::None)) = self.best_phases.get(&vi) {
                return Lit::from_assign(vi, *b);
            }
        }
        Lit::from_assign(vi, self.var[vi].is(Flag::PHASE))
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

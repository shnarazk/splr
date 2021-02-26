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
    fn select_staged_vars(
        &mut self,
        target: StagingTarget,
        rephasing: bool,
        neg_ion: usize,
        pos_ion: usize,
    );

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
    // #[cfg(feature = "var_staging")]
    // fn dissolve_staged_vars(&mut self, rephasing: bool) {
    //     self.rephasing = rephasing;
    //     for (vi, b) in self.staged_vars.iter() {
    //         let v = &mut self.var[*vi];
    //         v.set(Flag::PHASE, *b);
    //         v.extra_reward *= self.staging_reward_decay;
    //     }
    // }

    #[cfg(not(feature = "var_staging"))]
    fn num_ion(&self) -> usize {
        0
    }
    #[cfg(feature = "var_staging")]
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
    fn select_staged_vars(
        &mut self,
        mut target: StagingTarget,
        rephasing: bool,
        neg_ion: usize,
        pos_ion: usize,
    ) {
        self.rephasing = rephasing;
        self.stage_mode_select += 1;
        if !self.use_stage {
            return;
        }
        if target == StagingTarget::AutoSelect {
            target = StagingTarget::Clear;
            // if self.stage_mode_select % self.num_unreachables() == 0 {
            //     target = StagingTarget::Backbone;
            // }
            // if 0 == neg_ion {
            //     // target = StagingTarget::BestPhases;
            //     // target = StagingTarget::Ions;
            //     target = StagingTarget::Clear;
            // } else {
            //     target = StagingTarget::Backbone;
            // };
        }
        for vi in self.staged_vars.keys() {
            // self.var[*vi].extra_reward = 0.0;
            self.var[*vi].turn_off(Flag::STAGED);
        }
        self.staged_vars.clear();
        // let base = self.staging_reward_value; // or self.average_activity()
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
            StagingTarget::HighHalf => {
                let ave = self.average_activity();
                for (vi, (b, _)) in self.best_phases.iter() {
                    let v = &mut self.var[*vi];
                    if ave < v.reward && self.root_level < self.level[*vi] {
                        v.turn_on(Flag::STAGED);
                        v.set(Flag::PHASE, *b);
                        self.staged_vars.insert(*vi, *b);
                    }
                }
            }
            StagingTarget::Ions => {
                let AssignStack {
                    ref mut var,
                    ref best_phases,
                    ref level,
                    root_level,
                    ref mut staged_vars,
                    ref stage_activity,
                    ..
                } = self;

                let mut best_act_min: f64 = 100_000_000.0;
                for (vi, (_, r)) in best_phases.iter() {
                    if matches!(r, AssignReason::None) {
                        best_act_min = best_act_min.min(var[*vi].activity(*stage_activity));
                    }
                }

                for v in var.iter_mut().skip(1) {
                    if !v.is(Flag::ELIMINATED)
                        && *root_level < level[v.index]
                        && match best_phases.get(&v.index) {
                            // negative
                            Some((_, AssignReason::Implication(_, NULL_LIT))) => {
                                best_act_min <= v.activity(*stage_activity)
                            }
                            // positive
                            None => best_act_min <= v.activity(*stage_activity),
                            _ => false,
                        }
                    {
                        staged_vars.insert(v.index, v.is(Flag::PHASE));
                        v.turn_on(Flag::STAGED);
                    }
                }
            }
            StagingTarget::Random => {
                let limit = neg_ion.max(pos_ion) / 2;
                let _len = self.var_order.idxs[0].min(limit);
                for vi in self.var_order.heap[1..].iter().rev() {
                    let b = self.var[*vi].timestamp % 2 == 0;
                    self.staged_vars.insert(*vi, b);
                    self.var[*vi].turn_on(Flag::STAGED);
                }
            }
            #[cfg(feature = "explore_timestamp")]
            StagingTarget::Explore => {
                let since = self
                    .best_phases
                    .iter()
                    .map(|v| self.var[*v.0].assign_timestamp)
                    .min()
                    .unwrap_or(1);
                let len = self.var_order.idxs[0];
                for vi in self.var_order.heap[1..=len].iter() {
                    let v = &mut self.var[*vi];
                    if v.assign_timestamp < since {
                        self.staged_vars.insert(*vi, v.assign_timestamp % 2 == 0);
                        v.extra_reward = self.staging_reward_value;
                    }
                }
            }
            _ => (),
        }
    }
    fn select_decision_literal(&mut self) -> Lit {
        let vi = self.select_var();
        if self.use_rephase && self.rephasing {
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

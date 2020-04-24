/// Var Rewarding
use {
    super::{AssignStack, RewardStep},
    crate::types::*,
    std::slice::Iter,
};

#[cfg(feature = "use_core")]
use crate::state::SearchStrategy;

pub const VRD_MAX: f64 = 0.97;

/// a reward table used in VarDB::shift_reward_mode
///  - id: RewardStep
///  - start: lower bound of the range
///  - end: upper bound of the range
///  - scale: scaling coefficient for activity decay
pub const REWARDS: [(RewardStep, f64, f64, f64); 3] = [
    (RewardStep::HeatUp, 0.80, VRD_MAX, 0.0), // the last is dummy
    (RewardStep::Annealing, 0.96, VRD_MAX, 0.5),
    (RewardStep::Final, VRD_MAX, VRD_MAX, 0.5),
];

/// API for var rewarding.
pub trait VarRewardIF {
    /// return var's activity.
    fn activity(&mut self, vi: VarId) -> f64;
    /// initialize rewards based on an order of vars.
    fn initialize_reward(&mut self, iterator: Iter<'_, usize>);
    /// clear var's activity
    fn clear_reward(&mut self, vi: VarId);
    /// modify var's activity at conflict analysis in `analyze`.
    fn reward_at_analysis(&mut self, vi: VarId);
    /// modify var's activity at value assignment in `uncheck_{assume, enquue, fix}`.
    fn reward_at_assign(&mut self, vi: VarId);
    /// modify var's activity at value unassigment in `cancel_until`.
    fn reward_at_unassign(&mut self, vi: VarId);
    /// update internal counter.
    fn reward_update(&mut self);
}

impl VarRewardIF for AssignStack {
    #[inline]
    fn activity(&mut self, vi: VarId) -> f64 {
        self.var[vi].reward
    }
    fn initialize_reward(&mut self, iterator: Iter<'_, usize>) {
        #[cfg(not(feature = "EVSIDS"))]
        {
            // big bang initialization
            let mut v = 0.5;
            for vi in iterator {
                self.var[*vi].reward = v;
                v *= 0.9;
            }
        }
    }
    fn clear_reward(&mut self, vi: VarId) {
        self.var[vi].reward = 0.0;
    }
    //
    // EVSIDS
    //
    #[cfg(feature = "EVSIDS")]
    fn reward_at_analysis(&mut self, vi: VarId) {
        let s = self.reward_step;
        let t = self.ordinal;
        let v = &mut self.var[vi];
        if v.timestamp == t {
            return;
        }
        v.timestamp = t;
        v.reward += s;
        const SCALE: f64 = 1e-100;
        const SCALE_MAX: f64 = 1e100;
        if SCALE_MAX < v.reward {
            for v in &mut self.var[1..] {
                v.reward *= SCALE;
            }
            self.reward_step *= SCALE;
        }
    }
    #[cfg(feature = "EVSIDS")]
    fn reward_at_assign(&mut self, _: VarId) {}
    #[cfg(feature = "EVSIDS")]
    fn reward_at_unassign(&mut self, _: VarId) {}
    #[cfg(feature = "EVSIDS")]
    fn reward_update(&mut self) {
        self.ordinal += 1;
        const INC_SCALE: f64 = 1.01;
        self.reward_step *= INC_SCALE;
    }

    //
    // Learning Rate
    //
    #[cfg(not(feature = "EVSIDS"))]
    fn reward_at_analysis(&mut self, vi: VarId) {
        let v = &mut self.var[vi];
        v.participated += 1;
    }
    #[cfg(not(feature = "EVSIDS"))]
    fn reward_at_assign(&mut self, vi: VarId) {
        let t = self.ordinal;
        let v = &mut self.var[vi];
        v.timestamp = t;
    }
    #[cfg(not(feature = "EVSIDS"))]
    fn reward_at_unassign(&mut self, vi: VarId) {
        let v = &mut self.var[vi];
        let duration = (self.ordinal + 1 - v.timestamp) as f64;
        let decay = self.activity_decay;
        let rate = v.participated as f64 / duration;
        v.reward *= decay;
        v.reward += (1.0 - decay) * rate;
        v.participated = 0;
    }
    #[cfg(not(feature = "EVSIDS"))]
    // fn reward_update(&mut self) {
    //     const VRD_STEP: f64 = 0.000_01;
    //     self.ordinal += 1;
    //     self.activity_decay = self.activity_decay_max.min(self.activity_decay + VRD_STEP);
    // }
    fn reward_update(&mut self) {
        self.ordinal += 1;
        if self.activity_decay < self.activity_decay_max {
            self.activity_decay += self.reward_step;
            //} else if self.reward_mode != RewardStep::Final {
            //    let reward = &REWARDS[self.reward_mode as usize + 1];
            //    self.reward_mode = reward.0;
            //    self.activity_decay_max = reward.2;
            //    self.reward_step *= reward.3;
            //} else {
            //    self.activity_decay = self.activity_decay_max;
        }
    }
}

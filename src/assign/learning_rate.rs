/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {
    super::{AssignStack, Var},
    crate::types::*,
};

impl ActivityIF<VarId> for AssignStack {
    fn activity(&mut self, vi: VarId) -> f64 {
        self.var[vi].reward
    }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        self.var[vi].update_activity(self.ordinal, self.activity_decay, self.activity_anti_decay);
    }
    fn reward_at_assign(&mut self, vi: VarId) {
        self.var[vi].timestamp = self.ordinal;
    }
    #[inline]
    fn reward_at_propagation(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_unassign(&mut self, _vi: VarId) {}
    // Note: `update_rewards` should be called before `cancel_until`
    fn update_activity_tick(&mut self) {
        self.ordinal += 1;
    }
}

impl Var {
    fn update_activity(&mut self, t: usize, decay: f64, reward: f64) -> f64 {
        // Note: why the condition can be broken.
        //
        // 1. asg.ordinal += 1;
        // 1. handle_conflict -> cancel_until -> reward_at_unassign
        // 1. assign_by_implication -> v.timestamp = asg.ordinal
        // 1. restart
        // 1. cancel_until -> reward_at_unassign -> assertion failed
        //
        if self.timestamp < t {
            self.reward *= decay.powi((t - self.timestamp) as i32);
            self.timestamp = t;
        } else if 0.0 < reward {
            self.reward *= decay;
        }
        self.reward += reward;
        self.reward
    }
}

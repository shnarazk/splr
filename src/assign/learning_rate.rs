/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {
    super::{AssignStack, Var},
    crate::types::*,
};

impl ActivityIF<VarId> for AssignStack {
    fn activity(&mut self, vi: VarId) -> f64 {
        self.var[vi].activity(self.stage_activity)
    }
    fn average_activity(&self) -> f64 {
        self.activity_ema.get()
    }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        self.var[vi].participated += 1;
        self.activity_ema.update(self.var[vi].reward);
    }
    fn reward_at_assign(&mut self, vi: VarId) {
        self.var[vi].timestamp = self.ordinal;
    }
    fn reward_at_propagation(&mut self, _vi: VarId) {}
    fn reward_at_unassign(&mut self, vi: VarId) {
        self.var[vi].update_activity(self.ordinal, self.activity_decay, self.activity_anti_decay);
    }
    // Note: `update_rewards` should be called befere `cancel_until`
    fn update_rewards(&mut self) {
        self.ordinal += 1;
        self.stage_activity *= self.activity_decay;
    }
    fn update_activity_decay(&mut self, index: Option<usize>) {
        // asg.update_activity_decay();
        if let Some(index) = index {
            if self.reward_index < index {
                self.activity_decay += (1.0 - self.activity_decay) * self.activity_decay_step;
                self.reward_index += 1;
            }
        } else {
            self.activity_decay = self.activity_decay_default;
            self.reward_index = 1;
        }
        self.activity_anti_decay = 1.0 - self.activity_decay;
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
            let rate = self.participated as f64 / (t - self.timestamp) as f64;
            self.reward *= decay;
            self.reward += (1.0 - (rate - 1.0).powf(2.0)).powf(0.5) * reward;
            self.participated = 0;
            self.timestamp = t;
        }
        self.reward
    }
}

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
    // Note: `update_rewards` should be called befero `restart`
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
    // fn reward_actives(&mut self) {
    //     self.ordinal += 1;
    //     for lit in self.trail[self.len_upto(self.root_level)..].iter() {
    //         self.var[lit.vi()].update_activity(
    //             self.ordinal,
    //             self.activity_decay,
    //             self.activity_anti_decay,
    //         );
    //     }
    // }
}

impl Var {
    // Note: `update_rewards` should be called befero `restart`
    // Therefore timestamp must be smaller than t anytime.
    // But conflict_analyze can assert a new var.
    // So we can't expect v.timestamp < self.num_conflict.
    fn update_activity(&mut self, t: usize, decay: f64, reward: f64) -> f64 {
        if self.timestamp < t {
            let rate = self.participated as f64 / (t - self.timestamp) as f64;
            self.reward *= decay;
            self.reward += (1.0 - (rate - 1.0).powf(2.0)).powf(0.5) * reward;
            self.participated = 0;
            self.timestamp = t;
        }
        self.reward
    }
    #[cfg(not(feature = "var_staging"))]
    pub fn activity(&self, _: f64) -> f64 {
        self.reward
    }
    #[cfg(feature = "var_staging")]
    pub fn activity(&self, extra: f64) -> f64 {
        let val = self.reward;
        if self.is(Flag::STAGED) {
            val + extra
        } else {
            val
        }
    }
}

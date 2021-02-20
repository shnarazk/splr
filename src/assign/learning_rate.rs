/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
#[cfg(feature = "moving_var_reward_rate")]
#[cfg(feature = "strategy_adaptation")]
use crate::state::State;
use {
    super::{AssignStack, Var},
    crate::types::*,
};

impl ActivityIF<VarId> for AssignStack {
    #[inline]
    fn activity(&mut self, vi: VarId) -> f64 {
        let v = &mut self.var[vi];
        let val = v.reward;
        if v.is(Flag::STAGED) {
            val + self.stage_activity
        } else {
            val
        }
    }
    fn average_activity(&self) -> f64 {
        self.activity_ema.get()
    }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        self.var[vi].participated += 1.0;
        self.activity_ema.update(self.var[vi].reward);
    }
    fn reward_at_assign(&mut self, vi: VarId) {
        self.var[vi].timestamp = self.ordinal;
    }
    fn reward_at_propagation(&mut self, _vi: VarId) {
        // self.var[vi].participated = 0.0;
    }
    // Note: `update_rewards` should be called befero `restart`
    fn reward_at_unassign(&mut self, vi: VarId) {
        self.var[vi].update_activity(self.ordinal, self.activity_decay, self.activity_anti_decay);
    }
    fn update_rewards(&mut self) {
        self.ordinal += 1;
        self.stage_activity *= self.activity_decay;
    }

    #[cfg(feature = "moving_var_reward_rate")]
    fn update_activity_decay(&mut self) {
        // self.activity_decay = self
        //     .activity_decay_max
        //     .min(self.activity_decay + self.reward_step);
        // self.activity_anti_decay = 1.0 - self.activity_decay;
        // dbg!(&self.activity_decay);
        self.activity_decay = 0.5 * (self.activity_decay_max + self.activity_decay);
        self.activity_anti_decay = 1.0 - self.activity_decay;
    }
}

impl Var {
    // Note: `update_rewards` should be called befero `restart`
    // Therefore timestamp must be smaller than t anytime.
    // But conflict_analyze can assert a new var. So we can't expect v.timestamp < self.num_conflict
    fn update_activity(&mut self, t: usize, decay: f64, reward: f64) -> f64 {
        if self.timestamp < t {
            let duration = (t - self.timestamp) as f64;
            let rate = self.participated as f64 / duration as f64;
            self.reward *= decay.powf(duration);
            // self.reward += (1.0 + rate).log2() * reward;
            self.reward += rate * reward;
            self.participated = 0.0;
            self.timestamp = t;
        }
        self.reward
    }
}

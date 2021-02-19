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
        let val = v.update_activity(self.ordinal, self.activity_decay, 0.0);
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
        let r = self.var[vi].update_activity(
            self.ordinal,
            self.activity_decay,
            self.activity_anti_decay,
        );
        self.activity_ema.update(r);
    }
    fn reward_at_propagation(&mut self, vi: VarId) {
        self.var[vi].update_activity(
            self.ordinal,
            self.activity_decay,
            0.9 * self.activity_anti_decay,
        );
    }
    fn update_rewards(&mut self) {
        self.ordinal += 1;
        self.stage_activity *= self.activity_decay;
    }

    #[cfg(feature = "moving_var_reward_rate")]
    #[cfg(feature = "strategy_adaptation")]
    fn adjust_rewards(&mut self, state: &State) {
        if state.strategy.1 == self.num_conflict {
            match state.strategy.0 {
                SearchStrategy::LowDecisions => {
                    self.activity_decay_max -= 0.02;
                }
                SearchStrategy::HighSuccessive => {
                    self.activity_decay_max = (self.activity_decay_max + 0.005).min(0.999);
                }
                _ => (),
            };
        }
    }
    #[cfg(feature = "moving_var_reward_rate")]
    fn update_activity_decay(&mut self) {
        self.activity_decay = self
            .activity_decay_max
            .min(self.activity_decay + self.reward_step);
        self.activity_anti_decay = 1.0 - self.activity_decay;
    }
}

impl Var {
    fn update_activity(&mut self, t: usize, decay: f64, reward: f64) -> f64 {
        if self.timestamp < t {
            let duration = (t - self.timestamp) as f64;
            self.reward *= decay.powf(duration);
            self.reward += reward;
            self.timestamp = t;
        }
        self.reward
    }
}

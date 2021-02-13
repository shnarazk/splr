/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {super::AssignStack, crate::types::*};

impl ActivityIF<VarId> for AssignStack {
    #[inline]
    fn activity(&mut self, vi: VarId) -> f64 {
        let v = &self.var[vi];
        v.reward.max(v.extra_reward)
    }
    fn average_activity(&self) -> f64 {
        self.activity_ema.get()
    }
    fn clear_activity(&mut self, vi: VarId) {
        self.var[vi].reward = 0.0;
    }
    fn initialize_activity(&mut self, _ix: VarId) {}
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        let v = &mut self.var[vi];
        v.participated += 1;
    }
    fn reward_at_assign(&mut self, vi: VarId) {
        let t = self.ordinal;
        let v = &mut self.var[vi];
        v.timestamp = t;
        v.extra_reward *= self.staging_reward_decay;
    }
    fn reward_at_unassign(&mut self, vi: VarId) {
        let v = &mut self.var[vi];
        let duration = (self.ordinal + 1 - v.timestamp) as f64;
        let rate = v.participated as f64 / duration;
        v.reward *= self.activity_decay;
        v.reward += self.activity_anti_decay * rate.powf(self.occurrence_compression_rate);
        v.participated = 0;
        self.activity_ema.update(v.reward);
    }
    fn update_rewards(&mut self) {
        self.ordinal += 1;
        #[cfg(feature = "moving_var_reward_rate")]
        {
            self.activity_decay = self
                .activity_decay_max
                .min(self.activity_decay + self.reward_step);
        }
    }

    #[cfg(feature = "moving_var_reward_rate")]
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
}

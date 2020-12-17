/// Var Rewarding based on Learning Rate Rewardin gand Reason Side Rewarding
use {
    super::{AssignStack, VarRewardIF},
    crate::types::*,
    std::slice::Iter,
};

impl VarRewardIF for AssignStack {
    #[inline]
    fn activity(&self, vi: VarId) -> f64 {
        let v = &self.var[vi];
        v.reward + v.best_phase_reward
    }
    fn initialize_reward(&mut self, iterator: Iter<'_, usize>) {
        #[cfg(feature = "moving_var_reward_rate")]
        {
            self.reward_step = (self.activity_decay_max - self.activity_decay).abs() / 10_000.0;
        }
        // big bang initialization
        let mut v = 0.5;
        for vi in iterator {
            self.var[*vi].reward = v;
            v *= 0.99;
        }
        #[cfg(feature = "moving_var_reward_rate")]
        {
            self.activity_decay = self.activity_decay_max;
        }
    }
    fn expand_reward(&mut self, _: bool) {
        // const SCALE: f64 = 2.0;
        // let scale: f64 = if boost { 1.0 / SCALE } else { SCALE };
        for vi in 1..self.var.len() {
            let v = &mut self.var[vi];
            if v.is(Flag::REPHASE) {
                // v.reward = v.reward.powf(scale);
                v.set(Flag::PHASE, v.is(Flag::BEST_PHASE));
                v.best_phase_reward *= 0.9;
            }
        }
    }
    fn clear_reward(&mut self, vi: VarId) {
        self.var[vi].reward = 0.0;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        let v = &mut self.var[vi];
        v.participated += 1;
    }
    fn reward_at_assign(&mut self, vi: VarId) {
        let t = self.ordinal;
        let v = &mut self.var[vi];
        v.timestamp = t;
    }
    fn reward_at_unassign(&mut self, vi: VarId) {
        let v = &mut self.var[vi];
        let duration = (self.ordinal + 1 - v.timestamp) as f64;
        let decay = self.activity_decay;
        let rate = v.participated as f64 / duration;
        v.reward *= decay;
        v.reward += (1.0 - decay) * rate.powf(self.occurrence_compression_rate);
        v.participated = 0;
    }
    fn reward_update(&mut self) {
        self.ordinal += 1;
        #[cfg(feature = "moving_var_reward_rate")]
        {
            self.activity_decay = self
                .activity_decay_max
                .min(self.activity_decay + self.reward_step);
            // self.activity_decay = 1.0 - 1.0 / (1.0 + 0.5 * (self.num_restart as f64)).sqrt();
        }
    }
    #[cfg(feature = "moving_var_reward_rate")]
    fn adjust_reward(&mut self, state: &State) {
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

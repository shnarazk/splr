/// Var Rewarding based on Learning Rate Rewardin gand Reason Side Rewarding
use {
    super::{AssignStack, VarRewardIF},
    crate::{
        state::{SearchStrategy, State},
        types::*,
    },
    std::slice::Iter,
};

/// a pair of the start value and upper bound of var decay rate.
pub const REWARD_DECAY_RANGE: (f64, f64) = (0.10, 0.97);

impl VarRewardIF for AssignStack {
    #[inline]
    fn activity(&mut self, vi: VarId) -> f64 {
        self.var[vi].reward
    }
    fn initialize_reward(&mut self, iterator: Iter<'_, usize>) {
        self.activity_decay = REWARD_DECAY_RANGE.0;
        self.activity_decay_max = REWARD_DECAY_RANGE.1;
        self.reward_step = (REWARD_DECAY_RANGE.1 - REWARD_DECAY_RANGE.0).abs() / 10_000.0;
        // big bang initialization
        let mut v = 0.25;
        for vi in iterator {
            self.var[*vi].reward = v;
            v *= 0.99;
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
        let _decay = (1.0 - duration.ln() * (1.0 - self.activity_decay)).max(0.0);
        let rate = v.participated as f64 / duration;
        v.reward *= decay;
        v.reward += (1.0 - decay) * rate.sqrt();
        v.participated = 0;
    }
    fn reward_update(&mut self) {
        self.ordinal += 1;
        self.activity_decay = self
            .activity_decay_max
            .min(self.activity_decay + self.reward_step);
        // self.activity_decay = 1.0 - 1.0 / (1.0 + 0.5 * (self.num_restart as f64)).sqrt();
    }
    fn adjust_reward(&mut self, state: &State) {
        if state.strategy.1 == self.num_conflict {
            match state.strategy.0 {
                SearchStrategy::LowDecisions => {
                    self.activity_decay_max = REWARD_DECAY_RANGE.1 - 0.02;
                }
                SearchStrategy::HighSuccesive => {
                    self.activity_decay_max = REWARD_DECAY_RANGE.1 + 0.005;
                }
                _ => (),
            };
        }
    }
}

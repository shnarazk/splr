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
        self.var[vi].participated += 1;
    }
    fn reward_at_assign(&mut self, vi: VarId) {
        self.var[vi].timestamp = self.ordinal;
    }
    fn reward_at_propagation(&mut self, _vi: VarId) {}
    fn reward_at_unassign(&mut self, vi: VarId) {
        self.var[vi].update_activity(self.ordinal, self.activity_decay, self.activity_anti_decay);
    }
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
        const UPDATE_INTERVAL: u32 = 2;

        if self.timestamp < t {
            self.activated += (t - self.timestamp) as u32;
            self.timestamp = t;
        }
        if UPDATE_INTERVAL <= self.activated {
            self.reward *= decay;
            if 0 < self.participated {
                let rate = self.participated as f64 / self.activated as f64;
                // self.reward += (1.0 - (1.0 - rate).powi(2)) * reward;
                self.reward += rate * reward;
                self.participated = 0;
            }
            self.activated = 0;
            self.timestamp = t;
        }

        /* if self.timestamp < t {
            self.reward *= decay;
            if 0 < self.participated {
                let band: f64 = (t - self.timestamp) as f64;
                let rate = self.participated as f64 / band;
                let certainty = 1.0 - 0.6 / band;
                // self.reward += (1.0 - (1.0 - rate).powi(2)) * reward;
                self.reward += rate * certainty * reward;
                self.participated = 0;
            }
            self.timestamp = t;
        } */
        self.reward
    }
}

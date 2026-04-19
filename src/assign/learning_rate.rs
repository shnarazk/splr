/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {super::stack::AssignStack, crate::types::*};

impl ActivityIF<VarId> for AssignStack {
    #[inline]
    fn activity(&self, vi: VarId) -> f64 {
        if self.activity_decay == 1.0 || self.num_conflict == self.var[vi].last_conflict {
            self.var[vi].reward
        } else {
            let r = self.activity_decay * self.var[vi].reward;
            // let d = 1.0 / (self.num_conflict - self.var[vi].last_conflict) as f64;
            // r + self.activity_anti_decay * d
            r
        }
    }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        if self.activity_decay < 1.0 && self.num_conflict > self.var[vi].last_conflict {
            self.var[vi].reward *= self.activity_decay;
            self.var[vi].reward += 1.0 / (self.num_conflict - self.var[vi].last_conflict) as f64;
            self.max_reward_of_canceled_vars =
                self.max_reward_of_canceled_vars.max(self.var[vi].reward);
        }
    }
    #[inline]
    fn reward_at_assign(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_propagation(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_unassign(&mut self, _vi: VarId) {}
    fn set_learning_rate(&mut self, scaling: f64) {
        self.activity_decay = 1.0 - scaling;
        self.activity_anti_decay = scaling;
    }
    // Note: `update_rewards` should be called before `cancel_until`
    #[inline]
    fn update_activity_tick(&mut self) {
        self.tick += 1;
    }
}

impl AssignStack {
    pub fn rescale_activity(&mut self, scaling: f64) {
        for v in self.var.iter_mut().skip(1) {
            v.reward *= scaling;
        }
    }
}

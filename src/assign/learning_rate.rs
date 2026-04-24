/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {super::stack::AssignStack, crate::types::*};

impl ActivityIF<VarId> for AssignStack {
    #[inline]
    fn activity(&self, vi: VarId) -> f64 {
        if self.activity_decay == 1.0 || self.num_conflict == self.var[vi].last_used {
            self.var[vi].reward
        } else {
            let d0 = 1.0 / self.var[vi].reward;
            let d1 = (self.num_conflict - self.var[vi].last_used) as f64;
            if d1 < d0 {
                self.var[vi].reward
            } else {
                let d0 = 1.0 / self.var[vi].reward;
                let d1 = 2.0 * (self.num_conflict - self.var[vi].last_used) as f64;
                let s = self.activity_decay * d0 + self.activity_anti_decay * d1;
                1.0 / s
            }
        }
    }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    fn reward_to(&mut self, vi: VarId) {
        if self.activity_decay < 1.0 && self.num_conflict > self.var[vi].last_used {
            let d0 = 1.0 / self.var[vi].reward;
            let d1 = (self.num_conflict - self.var[vi].last_used) as f64;
            let s = self.activity_decay * d0 + self.activity_anti_decay * d1;
            self.var[vi].reward = 1.0 / s;

            // increment confllict counter
            self.var[vi].last_used = self.num_conflict;
            if self.max_reward_updated.1 < self.var[vi].reward {
                self.max_reward_updated.0 = self.var[vi].level;
                self.max_reward_updated.1 = self.var[vi].reward;
            }
        }
    }
    #[inline]
    fn reward_at_analysis(&mut self, vi: VarId) {
        self.reward_to(vi)
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

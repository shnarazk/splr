/// Var Rewarding based on EVSIDS
use {
    super::{AssignStack, Var},
    crate::types::*,
};

impl ActivityIF<VarId> for AssignStack<'_> {
    fn activity(&self, vi: VarId) -> f64 {
        self.var[vi].reward
    }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        let s = self.activity_decay_step;
        let t = self.ordinal;
        let v = &mut self.var[vi];
        if v.timestamp == t {
            return;
        }
        v.timestamp = t;
        v.reward += s;
        const SCALE: f64 = 1e-100;
        const SCALE_MAX: f64 = 1e100;
        if SCALE_MAX < v.reward {
            for v in &mut self.var[1..] {
                v.reward *= SCALE;
            }
            self.activity_decay_step *= SCALE;
        }
    }
    fn update_activity_decay(&mut self, _: f64) {
        self.activity_decay = self
            .activity_decay_default
            .min(self.activity_decay + self.activity_decay_step);
        self.activity_anti_decay = 1.0 - self.activity_decay;
    }
    fn update_activity_tick(&mut self) {
        const INC_SCALE: f64 = 1.01;
        if self.ordinal == 0 {
            self.activity_decay *= 0.5;
            self.activity_anti_decay = 1.0 - self.activity_decay;
        }
        self.ordinal += 1;
        self.activity_decay_step *= INC_SCALE;
    }
}

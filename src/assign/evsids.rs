/// Var Rewarding based on EVSIDS
use {
    super::{AssignStack, VarRewardIF},
    crate::{state::State, types::*},
    std::slice::Iter,
};

impl VarRewardIF for AssignStack {
    #[inline]
    fn activity(&self, vi: VarId) -> f64 {
        self.var[vi].reward
    }
    fn average_activity(&self) -> f64 {
        self.activity_ema.get()
    }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        let s = self.reward_step;
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
            self.reward_step *= SCALE;
        }
    }
    fn reward_update(&mut self) {
        self.ordinal += 1;
        const INC_SCALE: f64 = 1.01;
        self.reward_step *= INC_SCALE;
    }
    fn update_activity_decay(&mut self) {
        self.activity_decay = self
            .activity_decay_max
            .min(self.activity_decay + self.reward_step);
        self.activity_anti_decay = 1.0 - self.activity_decay;
    }
}

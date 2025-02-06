/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {
    super::stack::AssignStack,
    crate::{types::*, var_vector::*},
};

impl ActivityIF<VarId> for AssignStack {
    #[inline]
    fn activity(&self, vi: VarId) -> f64 {
        // self.var[vi].reward
        VarRef(vi).activity()
    }
    // fn activity_slow(&self, vi: VarId) -> f64 {
    //     self.var[vi].reward_ema.get()
    // }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        // self.var[vi].reward = val;
        VarRef(vi).set_activity(val);
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        // self.var[vi].turn_on(FlagVar::USED);
        VarRef(vi).turn_on(FlagVar::USED);
    }
    #[inline]
    fn reward_at_assign(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_propagation(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_unassign(&mut self, vi: VarId) {
        // self.var[vi].update_activity(self.activity_decay, self.activity_anti_decay);
        VarRef(vi).update_activity(self.activity_decay, self.activity_anti_decay);
    }
    fn update_activity_decay(&mut self, scaling: f64) {
        self.activity_decay = scaling;
        self.activity_anti_decay = 1.0 - scaling;
    }
    // Note: `update_rewards` should be called before `cancel_until`
    #[inline]
    fn update_activity_tick(&mut self) {
        self.tick += 1;
    }
}

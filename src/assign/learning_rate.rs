/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {
    super::{AssignStack, Var},
    crate::types::*,
};

impl ActivityIF<VarId> for AssignStack {
    #[inline]
    fn activity(&self, vi: VarId) -> f64 {
        self.var[vi].reward
    }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        self.var[vi].turn_on(FlagVar::USED);
    }
    #[inline]
    fn reward_at_assign(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_propagation(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_unassign(&mut self, vi: VarId) {
        self.var[vi].update_activity(self.activity_decay, self.activity_anti_decay);
    }
    // Note: `update_rewards` should be called before `cancel_until`
    #[inline]
    fn update_activity_tick(&mut self) {
        self.ordinal += 1;
    }
}

impl Var {
    fn update_activity(&mut self, decay: f64, reward: f64) -> f64 {
        // Note: why the condition can be broken.
        //
        // 1. asg.ordinal += 1;
        // 1. handle_conflict -> cancel_until -> reward_at_unassign
        // 1. assign_by_implication -> v.timestamp = asg.ordinal
        // 1. restart
        // 1. cancel_until -> reward_at_unassign -> assertion failed
        //
        self.reward *= decay;
        if self.is(FlagVar::USED) {
            self.reward += reward;
            self.turn_off(FlagVar::USED);
        }
        self.reward
    }
}

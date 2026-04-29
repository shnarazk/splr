/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {super::stack::AssignStack, crate::types::*};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum VarActivityScheme {
    #[default]
    LRB,
    VMTF,
}

impl ActivityIF<VarId> for AssignStack {
    #[inline]
    fn activity(&self, vi: VarId) -> f64 {
        match self.activity_scheme {
            VarActivityScheme::LRB => self.var[vi].reward,
            VarActivityScheme::VMTF => self.var[vi].last_conflict as f64,
        }
    }
    // fn activity_slow(&self, vi: VarId) -> f64 {
    //     self.var[vi].reward_ema.get()
    // }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        self.var[vi].reward = val;
    }
    #[inline]
    fn reward_to(&mut self, vi: VarId) -> f64 {
        // Note: why the condition can be broken.
        //
        // 1. asg.ordinal += 1;
        // 1. handle_conflict -> cancel_until -> reward_at_unassign
        // 1. assign_by_implication -> v.timestamp = asg.ordinal
        // 1. restart
        // 1. cancel_until -> reward_at_unassign -> assertion failed
        //
        let stay = self.activity_stay_rate;
        let reward = self.activity_learning_rate;
        self.var[vi].reward *= stay;
        if self.var[vi].is(FlagVar::USED) {
            self.var[vi].reward += reward;
            self.var[vi].turn_off(FlagVar::USED);
        }
        // self.var[vi].reward_ema.update(self.var[vi].reward);
        self.var[vi].reward
    }
    #[inline]
    fn reward_at_analysis(&mut self, vi: VarId) {
        self.var[vi].turn_on(FlagVar::USED);
    }
    #[inline]
    fn reward_at_assign(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_propagation(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_unassign(&mut self, vi: VarId) {
        self.reward_to(vi);
    }
    fn set_learning_rate(&mut self, scaling: f64) {
        self.activity_stay_rate = 1.0 - scaling;
        self.activity_learning_rate = scaling;
    }
    // Note: `update_rewards` should be called before `cancel_until`
    #[inline]
    fn update_activity_tick(&mut self) {
        self.tick += 1;
    }
}

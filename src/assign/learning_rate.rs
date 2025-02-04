/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {
    super::stack::AssignStack,
    crate::{types::*, var_vector::*},
};

impl ActivityIF<VarId> for AssignStack {
    #[inline]
    fn activity(&self, vi: VarId) -> f64 {
        // self.var[vi].reward
        VarRef(vi).reward()
    }
    // fn activity_slow(&self, vi: VarId) -> f64 {
    //     self.var[vi].reward_ema.get()
    // }
    fn set_activity(&mut self, vi: VarId, val: f64) {
        // self.var[vi].reward = val;
        VarRef(vi).set_reward(val);
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

impl AssignStack {
    pub fn rescale_activity(&mut self, scaling: f64) {
        for i in 1..self.num_vars {
            VarRef(i).set_reward(VarRef(i).reward() * scaling);
        }
    }
    // pub fn set_activity_trend(&mut self) -> f64 {
    //     let mut nv = 0;
    //     let mut inc = 0;
    //     let mut activity_sum: f64 = 0.0;
    //     // let mut dec = 1;
    //     for (vi, v) in self.var.iter_mut().enumerate().skip(1) {
    //         if v.is(FlagVar::ELIMINATED) || self.level[vi] == self.root_level {
    //             continue;
    //         }
    //         nv += 1;
    //         activity_sum += v.reward;
    //         let trend = v.reward_ema.trend();
    //         if 1.0 < trend {
    //             inc += 1;
    //         }
    //     }
    //     self.activity_averaged = activity_sum / nv as f64;
    //     self.cwss = inc as f64 / nv as f64;
    //     // println!("inc rate:{:>6.4}", self.cwss);
    //     self.cwss
    // }
}

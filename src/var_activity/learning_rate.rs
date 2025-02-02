/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use crate::types::*;

/// API for reward based activity management.
pub trait ActivityIF<Ix> {
    // /// return one's activity.
    // fn activity(&self, ix: Ix) -> f64;
    // /// set activity
    // fn set_activity(&mut self, ix: Ix, val: f64);
    /// modify one's activity at conflict analysis in `conflict_analyze` in [`solver`](`crate::solver`).
    fn reward_at_analysis(&mut self, _ix: &mut Ix) {
        #[cfg(feature = "boundary_check")]
        todo!()
    }
    /// modify one's activity at value assignment in assign.
    fn reward_at_assign(&mut self, _ix: &mut Ix) {
        #[cfg(feature = "boundary_check")]
        todo!()
    }
    /// modify one's activity at value assignment in unit propagation.
    fn reward_at_propagation(&mut self, _ix: &mut Ix) {
        #[cfg(feature = "boundary_check")]
        todo!()
    }
    /// modify one's activity at value un-assignment in [`cancel_until`](`crate::assign::PropagateIF::cancel_until`).
    fn reward_at_unassign(&mut self, _ix: &mut Ix) {
        #[cfg(feature = "boundary_check")]
        todo!()
    }
    /// update reward decay.
    fn update_activity_decay(&mut self, _decay: f64);
    /// update internal counter.
    fn update_activity_tick(&mut self);
    /// rescale all activities.
    fn rescale_activity(&mut self, vars: &mut [Ix], scaling: f64);
}

#[derive(Clone, Debug)]
pub struct VarActivityManager {
    /// var activity decay
    pub(super) activity_decay: f64,
    /// 1.0 - activity_decay
    pub(super) activity_anti_decay: f64,
    /// time stamp for activity
    pub(super) tick: usize,
}

impl Default for VarActivityManager {
    fn default() -> Self {
        VarActivityManager {
            activity_decay: 0.94,
            activity_anti_decay: 0.06,
            tick: 0,
        }
    }
}
impl Instantiate for VarActivityManager {
    fn instantiate(config: &Config, _cnf: &CNFDescription) -> Self {
        VarActivityManager {
            activity_decay: config.vrw_dcy_rat,
            activity_anti_decay: 1.0 - config.vrw_dcy_rat,
            ..VarActivityManager::default()
        }
    }
}

impl<'a> ActivityIF<Var<'a>> for VarActivityManager {
    // #[inline]
    // fn activity(&self, vi: VarId) -> f64 {
    //     self[vi].activity
    // }
    // fn activity_slow(&self, vi: VarId) -> f64 {
    //     self.var[vi].reward_ema.get()
    // }
    // fn set_activity(&mut self, vi: VarId, val: f64) {
    //     self[vi].activity = val;
    // }
    fn reward_at_analysis(&mut self, v: &mut Var) {
        v.turn_on(FlagVar::USED);
    }
    #[inline]
    fn reward_at_assign(&mut self, _v: &mut Var) {}
    #[inline]
    fn reward_at_propagation(&mut self, _v: &mut Var) {}
    #[inline]
    fn reward_at_unassign(&mut self, v: &mut Var) {
        v.update_activity(self.activity_decay, self.activity_anti_decay);
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
    fn rescale_activity(&mut self, vars: &mut [Var], scaling: f64) {
        for v in vars.iter_mut() {
            v.activity *= scaling;
        }
    }
}

// impl AssignStack {
//     pub fn set_activity_trend(&mut self) -> f64 {
//         let mut nv = 0;
//         let mut inc = 0;
//         let mut activity_sum: f64 = 0.0;
//         // let mut dec = 1;
//         for (vi, v) in self.var.iter_mut().enumerate().skip(1) {
//             if v.is(FlagVar::ELIMINATED) || self.level[vi] == self.root_level {
//                 continue;
//             }
//             nv += 1;
//             activity_sum += v.reward;
//             let trend = v.reward_ema.trend();
//             if 1.0 < trend {
//                 inc += 1;
//             }
//         }
//         self.activity_averaged = activity_sum / nv as f64;
//         self.cwss = inc as f64 / nv as f64;
//         // println!("inc rate:{:>6.4}", self.cwss);
//         self.cwss
//     }
// }

/// Var Rewarding based on Learning Rate Rewardin gand Reason Side Rewarding
use {
    super::{AssignStack, VarRewardIF},
    crate::{
        state::{SearchStrategy, State},
        types::*,
    },
    std::slice::Iter,
};

impl VarRewardIF for AssignStack {
    #[inline]
    fn activity(&mut self, vi: VarId) -> f64 {
        if self.stabilize {
            self.var[vi].reward_evsids
        } else {
            self.var[vi].reward_lr
        }
    }
    fn initialize_reward(&mut self, iterator: Iter<'_, usize>) {
        self.lr_decay_step = (self.activity_decay_max - self.activity_decay).abs() / 10_000.0;
        // big bang initialization
        let v = 0.0;
        for vi in iterator {
            self.var[*vi].reward_evsids = v;
            self.var[*vi].reward_lr = v;
            // v *= 0.99;
        }
    }
    fn clear_reward(&mut self, vi: VarId) {
        self.var[vi].reward_evsids = 0.0;
        self.var[vi].reward_lr = 0.0;
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        //
        //## EVSIDS
        //
        let s = self.evsids_reward_step;
        let v = &mut self.var[vi];
        v.reward_evsids += s;
        const SCALE: f64 = 1e-100;
        const SCALE_MAX: f64 = 1e100;
        if SCALE_MAX < v.reward_evsids {
            for v in &mut self.var[1..] {
                v.reward_evsids *= SCALE;
            }
            self.evsids_reward_step *= SCALE;
        }

        //
        //## LR
        //
        self.var[vi].participated += 1;
    }
    fn reward_at_assign(&mut self, vi: VarId) {
        //
        //## LR
        //
        self.var[vi].timestamp = self.ordinal;
    }
    fn reward_at_unassign(&mut self, vi: VarId) {
        //
        //## LR
        //
        let v = &mut self.var[vi];
        let duration = (self.ordinal + 1 - v.timestamp) as f64;
        let decay = self.activity_decay;
        let _decay = (1.0 - duration.ln() * (1.0 - self.activity_decay)).max(0.0);
        let rate = v.participated as f64 / duration;
        v.reward_lr *= decay;
        v.reward_lr += (1.0 - decay) * rate;
        v.participated = 0;
    }
    fn reward_update(&mut self) {
        //
        //## EVSIDS
        //
        self.ordinal += 1;
        const INC_SCALE: f64 = 1.01;
        self.evsids_reward_step *= INC_SCALE;

        //
        //## LR
        //
        self.ordinal += 1;
        self.activity_decay = self
            .activity_decay_max
            .min(self.activity_decay + self.lr_decay_step);
        // self.activity_decay = 1.0 - 1.0 / (1.0 + 0.5 * (self.num_restart as f64)).sqrt();
    }
    fn adjust_reward(&mut self, state: &State) {
        if state.strategy.1 == self.num_conflict {
            match state.strategy.0 {
                SearchStrategy::LowDecisions => {
                    self.activity_decay_max -= 0.02;
                }
                SearchStrategy::HighSuccesive => {
                    self.activity_decay_max = (self.activity_decay_max + 0.005).min(0.999);
                }
                _ => (),
            };
        }
    }
}

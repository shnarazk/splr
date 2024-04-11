#![cfg(feature = "clause_rewarding")]
use {super::ClauseRef, crate::types::*, std::num::NonZeroU32};

/// clause activity
/// Note: vivifier has its own conflict analyzer, which never call reward functions.

impl ActivityIF<ClauseRef> for ClauseDB {
    fn activity(&self, _cid: ClauseRef) -> f64 {
        unreachable!()
    }
    fn set_activity(&mut self, cid: ClauseRef, val: f64) {
        self[cid].reward = val;
    }
    #[inline]
    fn reward_at_analysis(&mut self, cr: ClauseRef) {
        let rcc = cr.get();
        let mut c = rcc.borrow_mut();
        c.update_activity(self.tick, self.activity_decay, self.activity_anti_decay);
    }
    fn update_activity_tick(&mut self) {
        self.tick += 1;
    }
    fn update_activity_decay(&mut self, decay: f64) {
        self.activity_decay = decay;
        self.activity_anti_decay = 1.0 - decay;
    }
}

impl Clause {
    #[inline]
    pub fn update_activity(&mut self, t: usize, decay: f64, reward: f64) -> f64 {
        if self.timestamp < t {
            self.reward *= decay.powi(t as i32 - self.timestamp as i32);
            self.reward += reward;
            self.timestamp = t;
        }
        self.reward
    }
}

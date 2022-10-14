#![cfg(feature = "clause_rewarding")]
use {super::ClauseId, crate::types::*, std::num::NonZeroU32};

// Note: vivifier has its own conflict analyzer, which never call reward functions.
impl ActivityIF<ClauseId> for ClauseDB {
    fn activity(&self, _cid: ClauseId) -> f64 {
        unreachable!()
    }
    fn set_activity(&mut self, cid: ClauseId, val: f64) {
        self[cid].reward = val;
    }
    #[inline]
    fn reward_at_analysis(&mut self, cid: ClauseId) {
        self.clause[NonZeroU32::get(cid.ordinal) as usize].update_activity(
            self.tick,
            self.activity_decay,
            self.activity_anti_decay,
        );
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

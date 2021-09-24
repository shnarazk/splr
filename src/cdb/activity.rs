use {super::ClauseId, crate::types::*};

// Note: vivifier has its own conflict analyzer, which never call reward functions.
impl ActivityIF<ClauseId> for ClauseDB {
    #[cfg(feature = "clause_rewarding")]
    fn activity(&mut self, cid: ClauseId) -> f64 {
        self.clause[std::num::NonZeroU32::get(cid.ordinal) as usize].update_activity(
            self.ordinal,
            self.activity_decay,
            0.0,
        )
    }
    #[cfg(not(feature = "clause_rewarding"))]
    fn activity(&mut self, _cid: ClauseId) -> f64 {
        0.0
    }
    #[cfg(feature = "clause_rewarding")]
    fn set_activity(&mut self, cid: ClauseId, val: f64) {
        self[cid].reward = val;
    }
    #[cfg(not(feature = "clause_rewarding"))]
    fn set_activity(&mut self, _cid: ClauseId, _val: f64) {}
    #[inline]
    fn reward_at_analysis(&mut self, cid: ClauseId) {
        self.clause[std::num::NonZeroU32::get(cid.ordinal) as usize].update_activity(
            self.ordinal,
            self.activity_decay,
            self.activity_anti_decay,
        );
    }
    fn update_activity_tick(&mut self) {
        self.ordinal += 1;
    }
}

impl Clause {
    #[inline]
    #[cfg(feature = "clause_rewarding")]
    pub fn update_activity(&mut self, t: usize, decay: f64, reward: f64) -> f64 {
        if self.timestamp < t {
            self.reward *= decay.powi(t as i32 - self.timestamp as i32);
            self.reward += reward;
            self.timestamp = t;
        }
        self.reward
    }
    #[cfg(not(feature = "clause_rewarding"))]
    pub fn update_activity(&mut self, _: usize, _: f64, _: f64) -> f64 {
        0.0
    }
}

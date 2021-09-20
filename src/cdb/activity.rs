use {super::ClauseId, crate::types::*};

// Note: vivifier has its own conflict analyzer, which never call reward functions.
impl ActivityIF<ClauseId> for ClauseDB {
    fn activity(&mut self, cid: ClauseId) -> f64 {
        self.clause[std::num::NonZeroU32::get(cid.ordinal) as usize].update_activity(
            self.ordinal,
            self.activity_decay,
            0.0,
        )
    }
    fn set_activity(&mut self, cid: ClauseId, val: f64) {
        self[cid].reward = val;
    }
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
    pub fn update_activity(&mut self, t: usize, decay: f64, reward: f64) -> f64 {
        if self.timestamp < t {
            self.reward *= decay.powi(t as i32 - self.timestamp as i32);
            self.reward += reward;
            self.timestamp = t;
        }
        self.reward
    }
}

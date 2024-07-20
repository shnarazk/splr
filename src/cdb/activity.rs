use {super::ClauseIndex, crate::types::*};

/// clause activity
/// Note: vivifier has its own conflict analyzer, which never call reward functions.

#[cfg(feature = "clause_rewarding")]
impl ActivityIF<ClauseIndex> for ClauseDB {
    fn activity(&self, _cid: ClauseIndex) -> f64 {
        unreachable!()
    }
    fn set_activity(&mut self, cid: ClauseIndex, val: f64) {
        self[cid].activity = val;
    }
    #[inline]
    fn reward_at_analysis(&mut self, cid: ClauseIndex) {
        self.clause[cid].update_activity(self.tick, self.activity_decay, self.activity_anti_decay);
    }
    fn update_activity_tick(&mut self) {
        self.tick += 1;
    }
    fn update_activity_decay(&mut self, decay: f64) {
        self.activity_decay = decay;
        self.activity_anti_decay = 1.0 - decay;
    }
}

#[cfg(not(feature = "clause_rewarding"))]
impl ActivityIF<ClauseIndex> for ClauseDB {
    #[inline]
    fn activity(&self, _cid: ClauseIndex) -> f64 {
        unreachable!()
    }
    fn set_activity(&mut self, _cid: ClauseIndex, _val: f64) {}
    fn reward_at_analysis(&mut self, _cid: ClauseIndex) {}
    fn update_activity_tick(&mut self) {}
    fn update_activity_decay(&mut self, _decay: f64) {}
}

#[cfg(feature = "clause_rewarding")]
impl Clause {
    #[inline]
    pub fn update_activity(&mut self, t: usize, decay: f64, reward: f64) -> f64 {
        if self.timestamp < t {
            self.activity *= decay.powi(t as i32 - self.timestamp as i32);
            self.activity += reward;
            self.timestamp = t;
        }
        self.activity
    }
}

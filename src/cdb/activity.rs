#![cfg(feature = "clause_rewarding")]
use {super::ClauseIndex, crate::types::*};

/// clause activity
/// Note: vivifier has its own conflict analyzer, which never call reward functions.

impl ActivityIF<ClauseIndex> for ClauseDB {
    fn activity(&self, ci: ClauseIndex) -> f64 {
        self[ci].timestamp as f64
    }
    fn set_activity(&mut self, _ci: ClauseIndex, _val: f64) {}
    #[inline]
    fn reward_at_analysis(&mut self, ci: ClauseIndex) {
        self.clause[ci].timestamp = self.tick;
    }
    fn reward_at_propagation(&mut self, _ci: ClauseIndex) {}
    fn update_activity_tick(&mut self) {
        self.tick += 1;
    }
    fn update_activity_decay(&mut self, _decay: f64) {}
}

impl Clause {
    pub(crate) fn activity(&self) -> f64 {
        self.timestamp as f64
    }
    #[inline]
    pub fn update_activity(&mut self, _tick: usize) {}
}

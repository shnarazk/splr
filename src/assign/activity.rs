/// Var Rewarding based on Learning Rate Rewarding and Reason Side Rewarding
use {super::AssignStack, crate::types::*};

impl ActivityIF<VarId> for AssignStack {
    #[inline]
    fn activity(&self, vi: VarId) -> f64 {
        self.var[vi].activity as f64
    }
    fn set_activity(&mut self, _vi: VarId, _: f64) {}
    fn reward_at_analysis(&mut self, vi: VarId) {
        // self.var[vi].activity = self.tick;
        self.var[vi].activity = self.tick.max(self.var[vi].activity + 1);
    }
    #[inline]
    fn reward_at_assign(&mut self, _vi: VarId) {}
    #[inline]
    fn reward_at_propagation(&mut self, _vi: VarId) {}
    fn reward_at_unassign(&mut self, vi: VarId) {
        if let Some(offset) = self.var[vi].activity.checked_sub(self.tick) {
            // self.var[vi].activity = self.tick + 1;
            self.var[vi].activity = self.tick + (offset as f64).sqrt() as usize;
        }
    }
    fn update_activity_decay(&mut self, _scaling: f64) {}
    // Note: `update_rewards` should be called before `cancel_until`
    #[inline]
    fn update_activity_tick(&mut self) {
        self.tick += 1;
    }
}

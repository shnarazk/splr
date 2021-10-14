#![cfg(feature = "trail_saving")]
/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{AssignStack, PropagateIF, VarHeapIF, VarManipulateIF},
    crate::{
        cdb::{self, ClauseDBIF},
        types::*,
    },
};

#[cfg(feature = "chrono_BT")]
use super::AssignIF;

const REASON_THRESHOLD: f64 = 1.5;

impl AssignStack {
    pub fn save_trail(&mut self, to_lvl: DecisionLevel) {
        let lim = self.trail_lim[to_lvl as usize];
        let dl = self.trail_lim.len();
        let mut free: usize = lim;
        self.clear_trail_saved();
        if 2 <= dl {
            let lim2 = self.trail_lim[dl - 2];
            let activity_threshold = self.var[self.trail[lim2].vi()].reward;
            for i in (lim..lim2).rev() {
                let l = self.trail[i];
                let vi = l.vi();

                //
                //## mutliple backtracks not work
                //
                // if let Some(i) = self.trail_saved.iter().position(|k| k.vi() == vi) {
                //     if self.trail_saved[i] == !l {
                //         self.trail_saved.drain(0..=i);
                //     }
                // }

                self.trail_saved.push(l);
                self.reason_saved[vi] = self.reason[vi];
                self.reward_at_unassign(vi);
                if activity_threshold <= self.var[vi].reward {
                    self.insert_heap(vi);
                }
            }
            free = lim2;
        }
        for i in free..self.trail.len() {
            let vi = self.trail[i].vi();
            self.reward_at_unassign(vi);
            self.insert_heap(vi);
        }
    }
    pub fn from_saved_trail(&mut self, cdb: &impl ClauseDBIF) -> PropagationResult {
        let q = (REASON_THRESHOLD * cdb.derefer(cdb::property::Tf64::DpAverageLBD)).max(6.0) as u16;

        #[cfg(feature = "chrono_BT")]
        let dl = self.decision_level();

        for i in (0..self.trail_saved.len()).rev() {
            let lit = self.trail_saved[i];
            let vi = lit.vi();
            let old_reason = self.reason_saved[vi];
            match (old_reason, self.assigned(lit)) {
                (_, Some(true)) => (),
                // reason refinement by ignoring this dependecy
                (AssignReason::Implication(c), None) if q < cdb[c].rank => {
                    self.insert_heap(vi);
                    return self.truncate_trail_saved(i + 1);
                }
                (AssignReason::BinaryLink(_) | AssignReason::Implication(_), None) => {
                    self.num_repropagation += 1;

                    #[cfg(feature = "chrono_BT")]
                    panic!("self.assign_by_implication(lit, dl, cid, NULL_LIT);");

                    #[cfg(not(feature = "chrono_BT"))]
                    self.assign_by_implication(lit, old_reason);
                }
                (AssignReason::BinaryLink(_) | AssignReason::Implication(_), Some(false)) => {
                    let _ = self.truncate_trail_saved(i + 1); // reduce heap ops.
                    self.clear_trail_saved();
                    return Err((lit, old_reason));
                }
                (AssignReason::Decision(_), _) => {
                    self.insert_heap(vi);
                    return self.truncate_trail_saved(i + 1);
                }
                r => panic!("impossible path {:?}", r),
            }
        }
        self.trail_saved.clear();
        Ok(())
    }
    pub fn clear_trail_saved(&mut self) {
        for j in 0..self.trail_saved.len() {
            let l = self.trail_saved[j];
            self.insert_heap(l.vi());
        }
        self.trail_saved.clear();
    }
    fn truncate_trail_saved(&mut self, len: usize) -> PropagationResult {
        self.trail_saved.truncate(len);
        Ok(())
    }
}

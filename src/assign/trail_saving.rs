#![cfg(feature = "trail_saving")]
/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{AssignStack, PropagateIF},
    crate::{cdb::ClauseDB, types::*, vam::VarActivityManager, var_vector::*},
};

#[cfg(feature = "chrono_BT")]
use super::AssignIF;

/// Methods on trail saving.
pub trait TrailSavingIF {
    fn save_trail(&mut self, to_lvl: DecisionLevel);
    fn reuse_saved_trail(&mut self, cdb: &ClauseDB) -> PropagationResult;
    fn clear_saved_trail(&mut self);
}

impl TrailSavingIF for AssignStack {
    fn save_trail(&mut self, to_lvl: DecisionLevel) {
        let lim = self.trail_lim[to_lvl as usize];
        let dl = self.trail_lim.len();
        let mut free: usize = lim;
        self.clear_saved_trail();
        if 2 <= dl {
            let lim2 = self.trail_lim[dl - 2];
            let activity_threshold = self.trail[lim2].var.activity;
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
                VarRef(vi).set_reason_saved(VarRef(vi).reason());
                VarActivityManager::reward_at_unassign(vi);
                if activity_threshold <= l.var.activity {
                    VarActivityManager::insert_heap(vi);
                }
            }
            free = lim2;
        }
        for i in free..self.trail.len() {
            let vi = self.trail[i].vi();
            VarActivityManager::reward_at_unassign(vi);
            VarActivityManager::insert_heap(vi);
        }
    }
    fn reuse_saved_trail(&mut self, cdb: &ClauseDB) -> PropagationResult {
        let q = self.stage_scale.trailing_zeros() as u16 + (cdb.lb_entanglement().get() as u16) / 2;

        #[cfg(feature = "chrono_BT")]
        let dl = self.decision_level();

        for i in (0..self.trail_saved.len()).rev() {
            let lit = self.trail_saved[i];
            let vi = lit.vi();
            let old_reason = lit.var.reason_saved;
            match (lit.lit_assigned(), old_reason) {
                (Some(true), _) => (),
                (None, AssignReason::BinaryLink(link)) => {
                    debug_assert_ne!(link.vi(), lit.vi());
                    debug_assert_eq!(link.lit_assigned(), Some(true));
                    self.num_repropagation += 1;

                    self.assign_by_implication(
                        lit,
                        old_reason,
                        #[cfg(feature = "chrono_BT")]
                        dl,
                    );
                }
                // reason refinement by ignoring this dependecy
                (None, AssignReason::Implication(c)) if q < cdb[c].rank => {
                    VarActivityManager::insert_heap(vi);
                    return self.truncate_trail_saved(i + 1);
                }
                (None, AssignReason::Implication(cid)) => {
                    debug_assert_eq!(cdb[cid].lit0(), lit);
                    debug_assert!(cdb[cid]
                        .iter()
                        .skip(1)
                        .all(|l| l.lit_assigned() == Some(false)));
                    self.num_repropagation += 1;

                    self.assign_by_implication(
                        lit,
                        old_reason,
                        #[cfg(feature = "chrono_BT")]
                        dl,
                    );
                }
                (Some(false), AssignReason::BinaryLink(link)) => {
                    debug_assert_ne!(link.vi(), lit.vi());
                    debug_assert_eq!(link.lit_assigned(), Some(true));
                    let _ = self.truncate_trail_saved(i + 1); // reduce heap ops.
                    self.clear_saved_trail();
                    return Err((lit, old_reason));
                }
                (Some(false), AssignReason::Implication(cid)) => {
                    debug_assert!(cdb[cid].iter().all(|l| l.lit_assigned() == Some(false)));
                    let _ = self.truncate_trail_saved(i + 1); // reduce heap ops.
                    self.clear_saved_trail();
                    return Err((cdb[cid].lit0(), AssignReason::Implication(cid)));
                }
                (_, AssignReason::Decision(lvl)) => {
                    debug_assert_ne!(0, lvl);
                    VarActivityManager::insert_heap(vi);
                    return self.truncate_trail_saved(i + 1);
                }
                _ => unreachable!("from_saved_trail"),
            }
        }
        self.trail_saved.clear();
        Ok(())
    }
    fn clear_saved_trail(&mut self) {
        for j in 0..self.trail_saved.len() {
            let l = self.trail_saved[j];
            VarActivityManager::insert_heap(l.vi());
        }
        self.trail_saved.clear();
    }
}

impl AssignStack {
    fn truncate_trail_saved(&mut self, len: usize) -> PropagationResult {
        self.trail_saved.truncate(len);
        Ok(())
    }
}

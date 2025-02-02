#![cfg(feature = "trail_saving")]
/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::AssignStack,
    crate::{cdb::ClauseDBIF, solver::VarActivityManager, types::*},
};

#[cfg(feature = "chrono_BT")]
use super::AssignIF;

/// Methods on trail saving.
pub trait TrailSavingIF<'a> {
    fn save_trail(
        &'a mut self,
        vars: &'a mut [Var<'a>],
        vam: &'a mut VarActivityManager,
        to_lvl: DecisionLevel,
    );
    fn reuse_saved_trail(&'a mut self, cdb: &'a ClauseDB) -> PropagationResult<'a>;
    fn clear_saved_trail(&'a mut self);
}

impl<'a> TrailSavingIF<'a> for AssignStack<'a> {
    fn save_trail(
        &'a mut self,
        vars: &'a mut [Var<'a>],
        vam: &'a mut VarActivityManager,
        to_lvl: DecisionLevel,
    ) {
        let lim = self.trail_lim[to_lvl as usize];
        let dl = self.trail_lim.len();
        let mut free: usize = lim;
        self.clear_saved_trail();
        if 2 <= dl {
            let lim2 = self.trail_lim[dl - 2];
            let activity_threshold = self.trail[lim2].var.activity;
            for i in (lim..lim2).rev() {
                let l = self.trail[i];
                let vi = l.var.id;

                //
                //## mutliple backtracks not work
                //
                // if let Some(i) = self.trail_saved.iter().position(|k| k.var.id == vi) {
                //     if self.trail_saved[i] == !l {
                //         self.trail_saved.drain(0..=i);
                //     }
                // }

                self.trail_saved.push(l);
                vam.reward_at_unassign(vars, vi);
                let v = &mut vars[vi];
                v.reason_saved = v.reason;
                if activity_threshold <= v.activity {
                    self.insert_heap(vi);
                }
            }
            free = lim2;
        }
        for i in free..self.trail.len() {
            let v = self.trail[i].var;
            vam.reward_at_unassign(vars, v.id);
            self.insert_heap(vi);
        }
    }
    fn reuse_saved_trail(&'a mut self, cdb: &'a ClauseDB) -> PropagationResult<'a> {
        let q = self.stage_scale.trailing_zeros() as u16
            + (cdb.derefer(crate::cdb::property::Tf64::LiteralBlockEntanglement) as u16) / 2;

        #[cfg(feature = "chrono_BT")]
        let dl = self.decision_level();

        for i in (0..self.trail_saved.len()).rev() {
            let lit = self.trail_saved[i];
            let vi = lit.var.id;
            let old_reason = lit.var.reason_saved;
            match (lit.assigned(), old_reason) {
                (Some(true), _) => (),
                (None, AssignReason::BinaryLink(link)) => {
                    debug_assert_ne!(link.var.id, lit.var.id);
                    debug_assert_eq!(link.assigned(), Some(true));
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
                    self.insert_heap(vi);
                    return self.truncate_trail_saved(i + 1);
                }
                (None, AssignReason::Implication(cid)) => {
                    debug_assert_eq!(cdb[cid].lit0(), lit);
                    debug_assert!(cdb[cid].iter().skip(1).all(|l| l.assigned() == Some(false)));
                    self.num_repropagation += 1;

                    self.assign_by_implication(
                        lit,
                        old_reason,
                        #[cfg(feature = "chrono_BT")]
                        dl,
                    );
                }
                (Some(false), AssignReason::BinaryLink(link)) => {
                    debug_assert_ne!(link.var.id, lit.var.id);
                    debug_assert_eq!(link.assigned(), Some(true));
                    let _ = self.truncate_trail_saved(i + 1); // reduce heap ops.
                    self.clear_saved_trail();
                    return Err((lit, old_reason));
                }
                (Some(false), AssignReason::Implication(cid)) => {
                    debug_assert!(cdb[cid].iter().all(|l| l.assigned() == Some(false)));
                    let _ = self.truncate_trail_saved(i + 1); // reduce heap ops.
                    self.clear_saved_trail();
                    return Err((cdb[cid].lit0(), AssignReason::Implication(cid)));
                }
                (_, AssignReason::Decision(lvl)) => {
                    debug_assert_ne!(0, lvl);
                    self.insert_heap(vi);
                    return self.truncate_trail_saved(i + 1);
                }
                _ => unreachable!("from_saved_trail"),
            }
        }
        self.trail_saved.clear();
        Ok(())
    }
    fn clear_saved_trail(&'a mut self) {
        for j in 0..self.trail_saved.len() {
            let l = self.trail_saved[j];
            self.insert_heap(l.var.id);
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

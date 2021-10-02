/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
    crate::{
        cdb::{self, ClauseDBIF},
        types::*,
    },
};

#[cfg(feature = "trail_saving")]
impl AssignStack {
    pub fn save_trail(&mut self, lim: usize, to_lvl: DecisionLevel) {
        let dl = self.trail_lim.len();

        //
        //## mutliple backtracks
        //
        if true || to_lvl == self.root_level {
            self.trail_saved.clear();
        }

        if 2 <= dl {
            let lim2 = self.trail_lim[dl - 2];
            for i in (lim..lim2).rev() {
                let l = self.trail[i];
                let vi = l.vi();

                //
                //## mutliple backtracks
                //
                // if let Some(i) = self.trail_saved.iter().position(|k| k.vi() == vi) {
                //     if self.trail_saved[i] == l {
                //         // self.trail_saved.remove(i);
                //         self.trail_saved.drain(0..=i);
                //     } else {
                //         self.trail_saved.drain(0..=i);
                //     }
                // }

                self.trail_saved.push(l);
                self.reason_saved[vi] = self.reason[vi];
            }
        }
    }
    pub fn from_saved_trail<C>(&mut self, cdb: &C) -> Option<ConflictContext>
    where
        C: ClauseDBIF,
    {
        let q = (0.75 * cdb.derefer(cdb::property::Tf64::DpAverageLBD)).max(4.0) as u16;
        let dl = self.decision_level();
        for i in (0..self.trail_saved.len()).rev() {
            let lit = self.trail_saved[i];
            let vi = lit.vi();
            let old_reason = self.reason_saved[vi];
            match (old_reason, self.assigned(lit)) {
                (_, Some(true)) => (),
                // reason refinement by ignoring this dependecy like decision var
                (AssignReason::Implication(c, l), None) if l == NULL_LIT && q < cdb[c].rank => {
                    self.trail_saved.truncate(i + 1);
                    return None;
                }
                (AssignReason::Implication(cid, l), None) => {
                    self.num_repropagation += 1;
                    self.assign_by_implication(lit, dl, cid, l);
                }
                (AssignReason::Implication(cid, link), Some(false)) => {
                    self.trail_saved.clear();
                    if link == NULL_LIT {
                        return Some(ConflictContext { cid, link });
                    }
                    if self.reason[vi] == old_reason {
                        return Some(ConflictContext { cid, link });
                    } else {
                        return Some(ConflictContext {
                            cid,
                            link: cdb[cid].lit0(),
                        });
                    }
                }
                (AssignReason::Decision(_), _) => {
                    self.trail_saved.truncate(i + 1);
                    return None;
                }
                r => panic!("impossible path {:?}", r),
            }
        }
        self.trail_saved.clear();
        None
    }
    pub fn clear_saved_trail(&mut self) {
        self.trail_saved.clear();
    }
}

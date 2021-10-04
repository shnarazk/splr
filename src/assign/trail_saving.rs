/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{AssignIF, AssignStack, PropagateIF, VarHeapIF, VarManipulateIF},
    crate::{
        cdb::{self, ClauseDBIF},
        types::*,
    },
};

#[cfg(feature = "trail_saving")]
impl AssignStack {
    pub fn save_trail(&mut self, lim: usize, _to_lvl: DecisionLevel) {
        let dl = self.trail_lim.len();
        let mut free: usize = lim;
        //
        //## mutliple backtracks
        //
        /* if true || to_lvl == self.root_level */
        {
            self.clear_trail_saved();
        }

        if 2 <= dl {
            let lim2 = self.trail_lim[dl - 2];
            let r = self.var[self.trail[lim2].vi()].reward;
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
                self.reward_at_unassign(vi);
                if r <= self.var[vi].reward {
                    self.insert_heap(l.vi());
                }
                /* if self.var[vi].is(Flag::USED) {
                    self.insert_heap(l.vi());
                } else if let AssignReason::Decision(_) = self.reason[vi] {
                    self.insert_heap(l.vi());
                } */
            }
            free = lim2;
        }
        for i in free..self.trail.len() {
            let vi = self.trail[i].vi();
            self.reward_at_unassign(vi);
            self.insert_heap(vi);
        }
    }
    pub fn from_saved_trail<C>(&mut self, cdb: &C) -> Option<ConflictContext>
    where
        C: ClauseDBIF,
    {
        let q = (1.2 * cdb.derefer(cdb::property::Tf64::DpAverageLBD)).max(5.0) as u16;
        let dl = self.decision_level();
        for i in (0..self.trail_saved.len()).rev() {
            let lit = self.trail_saved[i];
            let vi = lit.vi();
            let old_reason = self.reason_saved[vi];
            match (old_reason, self.assigned(lit)) {
                (_, Some(true)) => (),
                // reason refinement by ignoring this dependecy like decision var
                (AssignReason::Implication(c, NULL_LIT), None) if q < cdb[c].rank => {
                    self.insert_heap(vi);
                    return self.truncate_trail_saved(i + 1);
                }
                (AssignReason::Implication(cid, NULL_LIT), None) => {
                    debug_assert_eq!(cdb[cid].lit0(), lit);
                    debug_assert!(
                        cdb[cid]
                            .iter()
                            .skip(1)
                            .all(|l| self.assigned(*l) == Some(false)),
                        "{:?}",
                        self.dump(cdb, cid),
                    );
                    self.num_repropagation += 1;
                    self.assign_by_implication(lit, dl, cid, NULL_LIT);
                }
                (AssignReason::Implication(cid, l), None) => {
                    debug_assert!(
                        cdb[cid].lit0() != l || self.assigned(cdb[cid].lit0()) == Some(true),
                        "{:?}",
                        self.dump(cdb, cid)
                    );
                    debug_assert!(
                        cdb[cid].lit1() != l || self.assigned(cdb[cid].lit1()) == Some(true),
                        "{:?}",
                        self.dump(cdb, cid),
                    );
                    self.num_repropagation += 1;
                    self.assign_by_implication(lit, dl, cid, l);
                }
                (AssignReason::Implication(cid, link), Some(false)) => {
                    self.truncate_trail_saved(i + 1);
                    self.clear_trail_saved();
                    debug_assert!(
                        cdb[cid].iter().all(|l| self.assigned(*l) == Some(false)),
                        "## {} ##\n{}\n{:?}",
                        i32::from(lit),
                        self.dump(cdb, cid),
                        old_reason,
                    );
                    if link == NULL_LIT {
                        return Some(ConflictContext { cid, link });
                    }
                    let c = &cdb[cid];
                    let lit0 = c.lit0();
                    return Some(ConflictContext {
                        cid,
                        link: if lit != lit0 { lit0 } else { c.lit1() },
                    });
                }
                (AssignReason::Decision(_), _) => {
                    self.insert_heap(vi);
                    return self.truncate_trail_saved(i + 1);
                }
                r => panic!("impossible path {:?}", r),
            }
        }
        self.trail_saved.clear();
        None
    }
    fn dump<C>(&self, cdb: &C, cid: ClauseId) -> String
    where
        C: ClauseDBIF,
    {
        cdb[cid]
            .iter()
            .map(|l| format!("{}:{:?}", l, self.assigned(*l)))
            .collect::<Vec<String>>()
            .join("\n")
    }
    pub fn clear_trail_saved(&mut self) {
        for j in 0..self.trail_saved.len() {
            let l = self.trail_saved[j];
            self.insert_heap(l.vi());
        }
        self.trail_saved.clear();
    }
    fn truncate_trail_saved(&mut self, len: usize) -> Option<ConflictContext> {
        self.trail_saved.truncate(len);
        None
    }
}

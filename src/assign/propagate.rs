/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{AssignIF, AssignStack, VarHeapIF, VarRewardIF},
    crate::{
        clause::{ClauseDBIF, WatchDBIF},
        types::*,
    },
};

/// API for assignment like `propagate`, `enqueue`, `cancel_until`, and so on.
pub trait PropagateIF {
    /// add an assignment at level 0 as a precondition.
    ///
    /// # Errors
    ///
    /// emit `SolverError::Inconsistent` exception if solver becomes inconsistent.
    fn assign_at_rootlevel(&mut self, l: Lit) -> MaybeInconsistent;
    /// unsafe enqueue (assign by implication); doesn't emit an exception.
    ///
    /// ## Warning
    /// Caller must assure the consistency after this assignment
    fn assign_by_implication(&mut self, l: Lit, reason: AssignReason, lv: DecisionLevel);
    /// unsafe assume (assign by decision); doesn't emit an exception.
    /// ## Caveat
    /// Callers have to assure the consistency after this assignment.
    fn assign_by_decision(&mut self, l: Lit);
    /// fix a var's assignment by a unit learnt clause.
    /// ## Caveat
    /// - Callers have to assure the consistency after this assignment.
    /// - No need to restart; but execute `propagate` just afterward.
    fn assign_by_unitclause(&mut self, l: Lit);
    /// execute *backjump*.
    fn cancel_until(&mut self, lv: DecisionLevel);
    /// execute *boolean constraint propagation* or *unit propagation*.
    fn propagate<C>(&mut self, cdb: &mut C) -> ClauseId
    where
        C: ClauseDBIF;
    /// reset or copy phase data.
    fn reset_assign_record(&mut self, flag: Flag, from: Option<Flag>);
}

macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
    };
}

macro_rules! lit_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l => {
                #[allow(unused_unsafe)]
                // unsafe { *$asg.asgvec.get_unchecked(l.vi()) ^ (l as u8 & 1) }
                match unsafe { *$asg.assign.get_unchecked(l.vi()) } {
                    Some(x) if !bool::from(l) => Some(!x),
                    x => x,
                }
            }
        }
    };
}

macro_rules! set_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l => unsafe {
                *$asg.assign.get_unchecked_mut(l.vi()) = Some(bool::from(l));
            },
        }
    };
}

macro_rules! unset_assign {
    ($asg: expr, $var: expr) => {
        unsafe {
            *$asg.assign.get_unchecked_mut($var) = None;
        }
    };
}

impl PropagateIF for AssignStack {
    fn assign_at_rootlevel(&mut self, l: Lit) -> MaybeInconsistent {
        let vi = l.vi();
        debug_assert!(vi < self.var.len());
        self.level[vi] = 0;
        debug_assert!(!self.var[vi].is(Flag::ELIMINATED));
        debug_assert_eq!(self.root_level, self.decision_level());
        match var_assign!(self, vi) {
            None => {
                set_assign!(self, l);
                self.reason[vi] = AssignReason::None;
                debug_assert!(!self.trail.contains(&!l));
                self.trail.push(l);
                Ok(())
            }
            Some(x) if x == bool::from(l) => Ok(()),
            _ => Err(SolverError::Inconsistent),
        }
    }
    fn assign_by_implication(&mut self, l: Lit, reason: AssignReason, lv: DecisionLevel) {
        debug_assert!(usize::from(l) != 0, "Null literal is about to be equeued");
        debug_assert!(l.vi() < self.var.len());
        // The following doesn't hold anymore by using chronoBT.
        // assert!(self.trail_lim.is_empty() || cid != ClauseId::default());
        let vi = l.vi();
        self.level[vi] = lv;
        let v = &mut self.var[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        debug_assert!(
            var_assign!(self, vi) == Some(bool::from(l)) || var_assign!(self, vi).is_none()
        );
        set_assign!(self, l);
        self.reason[vi] = reason;
        self.reward_at_assign(vi);
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
    }
    fn assign_by_decision(&mut self, l: Lit) {
        debug_assert!(l.vi() < self.var.len());
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l), format!("{:?}", l));
        self.level_up();
        let dl = self.trail_lim.len() as DecisionLevel;
        let vi = l.vi();
        self.level[vi] = dl;
        let v = &mut self.var[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        // debug_assert!(self.assign[vi] == l.lbool() || self.assign[vi] == BOTTOM);
        set_assign!(self, l);
        self.reason[vi] = AssignReason::default();
        self.reward_at_assign(vi);
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
    }
    fn assign_by_unitclause(&mut self, l: Lit) {
        self.cancel_until(self.root_level);
        debug_assert!(self.trail.iter().all(|k| k.vi() != l.vi()));
        let vi = l.vi();
        self.level[vi] = 0;
        set_assign!(self, l);
        self.reason[vi] = AssignReason::default();
        self.clear_reward(l.vi());
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
    }
    fn cancel_until(&mut self, lv: DecisionLevel) {
        if self.trail_lim.len() as u32 <= lv {
            return;
        }
        let lim = self.trail_lim[lv as usize];
        let mut shift = lim;
        for i in lim..self.trail.len() {
            let l = self.trail[i];
            let vi = l.vi();
            if self.level[vi] <= lv {
                self.trail[shift] = l;
                shift += 1;
                continue;
            }
            let v = &mut self.var[vi];
            v.set(Flag::PHASE, var_assign!(self, vi).unwrap());
            unset_assign!(self, vi);
            self.reason[vi] = AssignReason::default();
            self.reward_at_unassign(vi);
            self.insert_heap(vi);
        }
        self.trail.truncate(shift);
        debug_assert!(self
            .trail
            .iter()
            .all(|l| var_assign!(self, l.vi()).is_some()));
        debug_assert!(self.trail.iter().all(|k| !self.trail.contains(&!*k)));
        self.trail_lim.truncate(lv as usize);
        // assert!(lim < self.q_head) dosen't hold sometimes in chronoBT.
        self.q_head = self.q_head.min(lim);
        if lv == self.root_level {
            self.num_restart += 1;
        }
    }
    /// UNIT PROPAGATION.
    /// Note:
    ///  - *Precondition*: no checking dead clauses. They cause crash.
    ///  - This function assumes there's no dead clause.
    ///    So Eliminator should call `garbage_collect` before me.
    ///  - The order of literals in binary clauses will be modified to hold
    ///    propagatation order.
    fn propagate<C>(&mut self, cdb: &mut C) -> ClauseId
    where
        C: ClauseDBIF,
    {
        let watcher = cdb.watcher_lists_mut() as *mut [Vec<Watch>];
        unsafe {
            self.num_propagation += 1;
            while let Some(p) = self.trail.get(self.q_head) {
                self.q_head += 1;
                let false_lit = !*p;
                let source = (*watcher).get_unchecked_mut(usize::from(*p));
                let mut n = 0;
                'next_clause: while n < source.len() {
                    let w = source.get_unchecked_mut(n);
                    n += 1;
                    let blocker_value = lit_assign!(self, w.blocker);
                    if blocker_value == Some(true) {
                        continue 'next_clause;
                    }
                    if w.binary {
                        if blocker_value == Some(false) {
                            self.conflicts.1 = self.conflicts.0;
                            self.conflicts.0 = false_lit.vi();
                            self.num_conflict += 1;
                            return w.c;
                        }
                        self.assign_by_implication(
                            w.blocker,
                            AssignReason::Implication(w.c, false_lit),
                            self.level[false_lit.vi()],
                        );
                        continue 'next_clause;
                    }
                    // debug_assert!(!cdb[w.c].is(Flag::DEAD));
                    let Clause {
                        ref mut lits,
                        ref mut search_from,
                        ..
                    } = cdb[w.c];
                    debug_assert!(lits[0] == false_lit || lits[1] == false_lit);
                    let mut first = *lits.get_unchecked(0);
                    if first == false_lit {
                        first = *lits.get_unchecked(1);
                        lits.swap(0, 1);
                    }
                    let first_value = lit_assign!(self, first);
                    if first != w.blocker && first_value == Some(true) {
                        w.blocker = first;
                        continue 'next_clause;
                    }
                    //
                    //## Search an un-falsified literal
                    //
                    #[cfg(feature = "boundary_check")]
                    assert!(*search_from < lits.len());
                    for (start, end) in &[(*search_from + 1, lits.len()), (2, *search_from + 1)] {
                        for k in *start..*end {
                            let lk = &lits[k];
                            if lit_assign!(self, *lk) != Some(false) {
                                (*watcher)
                                    .get_unchecked_mut(usize::from(!*lk))
                                    .register(first, w.c, false);
                                n -= 1;
                                source.detach(n);
                                lits.swap(1, k);
                                // *search_from = k + 1;
                                *search_from = k;
                                continue 'next_clause;
                            }
                        }
                    }

                    if first_value == Some(false) {
                        self.conflicts.1 = self.conflicts.0;
                        self.conflicts.0 = false_lit.vi();
                        self.num_conflict += 1;
                        return w.c;
                    }
                    let lv = lits[1..]
                        .iter()
                        .map(|l| self.level[l.vi()])
                        .max()
                        .unwrap_or(0);
                    self.assign_by_implication(first, AssignReason::Implication(w.c, NULL_LIT), lv);
                }
            }
        }
        let na = self.trail.len() + self.num_eliminated_vars;
        // if self.num_target_assign < na {
        //     self.target_assign = true;
        //     self.num_target_assign = na;
        //     self.save_phase(Flag::TARGET_PHASE, self.build_target_at + 1 == self.num_propagation);
        //     self.build_target_at = self.num_propagation;
        // }
        if self.num_best_assign < na {
            self.best_assign = true;
            self.num_best_assign = na;
            self.save_phase(
                Flag::BEST_PHASE,
                self.build_best_at + 1 == self.num_propagation,
            );
            self.build_best_at = self.num_propagation;
        }
        ClauseId::default()
    }
    fn reset_assign_record(&mut self, flag: Flag, from: Option<Flag>) {
        match flag {
            Flag::PHASE => {
                if let Some(source) = from {
                    for v in self.var.iter_mut().skip(1) {
                        v.set(flag, v.is(source));
                    }
                }
            }
            Flag::BEST_PHASE => {
                if let Some(source) = from {
                    for v in self.var.iter_mut().skip(1) {
                        v.set(flag, v.is(source));
                    }
                    self.build_best_at = self.num_propagation;
                } else {
                    self.num_best_assign = 0;
                }
            }
            Flag::TARGET_PHASE => {
                self.num_target_assign = self.num_eliminated_vars;
                if let Some(source) = from {
                    for v in self.var.iter_mut().skip(1) {
                        v.set(flag, v.is(source));
                    }
                }
            }
            _ => panic!("invalid flag for reset_assign_record"),
        }
    }
}

impl AssignStack {
    fn level_up(&mut self) {
        self.trail_lim.push(self.trail.len());
    }
    fn save_phase(&mut self, flag: Flag, incremental: bool) {
        let to = if incremental && 0 < self.decision_level() {
            self.len_upto(self.decision_level() - 1)
        } else {
            0
        };
        for l in self.trail.iter().skip(to) {
            self.var[l.vi()].set(flag, bool::from(*l));
        }
    }
}

/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{AssignIF, AssignStack, VarHeapIF},
    crate::{
        cdb::{ClauseDBIF, WatchDBIF},
        types::*,
    },
};

/// API for Boolean Constraint Propagation like [`propagate`](`crate::assign::PropagateIF::propagate`), [`assign_by_decision`](`crate::assign::PropagateIF::assign_by_decision`), [`cancel_until`](`crate::assign::PropagateIF::cancel_until`), and so on.
pub trait PropagateIF {
    /// add an assignment at level 0 as a precondition.
    ///
    /// # Errors
    ///
    /// emit `SolverError::Inconsistent` exception if solver becomes inconsistent.
    fn assign_at_root_level(&mut self, l: Lit) -> MaybeInconsistent;
    /// unsafe enqueue (assign by implication); doesn't emit an exception.
    ///
    /// ## Warning
    /// Callers must assure the consistency after this assignment.
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
    /// execute backjump in vivifiacion sandbox
    fn backtrack_sandbox(&mut self);
    /// execute *boolean constraint propagation* or *unit propagation*.
    fn propagate<C>(&mut self, cdb: &mut C) -> ClauseId
    where
        C: ClauseDBIF;
    /// `propagate` for vivification, which allows dead clauses.
    fn propagate_sandbox<C>(&mut self, cdb: &mut C) -> ClauseId
    where
        C: ClauseDBIF;
}

macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
    };
}

macro_rules! lit_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l =>
            {
                #[allow(unused_unsafe)]
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
                let vi = l.vi();
                *$asg.assign.get_unchecked_mut(vi) = Some(bool::from(l));
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
    fn assign_at_root_level(&mut self, l: Lit) -> MaybeInconsistent {
        let vi = l.vi();
        debug_assert!(vi < self.var.len());
        debug_assert!(!self.var[vi].is(Flag::ELIMINATED));
        debug_assert_eq!(self.root_level, self.decision_level());
        debug_assert!(self.trail_lim.is_empty());
        self.level[vi] = self.root_level;
        match var_assign!(self, vi) {
            None => {
                set_assign!(self, l);
                self.reason[vi] = AssignReason::None;
                debug_assert!(!self.trail.contains(&!l));
                self.trail.push(l);
                self.make_var_asserted(vi);
                Ok(())
            }
            Some(x) if x == bool::from(l) => {
                // Vivification tries to assign a var by propagation then can assert it.
                // To make sure the var is asserted, we need to nullify its reason.
                self.reason[vi] = AssignReason::None;
                // self.make_var_asserted(vi);
                Ok(())
            }
            _ => Err(SolverError::Inconsistent),
        }
    }
    fn assign_by_implication(&mut self, l: Lit, reason: AssignReason, lv: DecisionLevel) {
        debug_assert!(usize::from(l) != 0, "Null literal is about to be enqueued");
        debug_assert!(l.vi() < self.var.len());
        // The following doesn't hold anymore by using chronoBT.
        // assert!(self.trail_lim.is_empty() || !cid.is_none());
        let vi = l.vi();
        debug_assert!(!self.var[vi].is(Flag::ELIMINATED));
        debug_assert!(
            var_assign!(self, vi) == Some(bool::from(l)) || var_assign!(self, vi).is_none()
        );
        set_assign!(self, l);
        self.level[vi] = lv;
        self.reason[vi] = reason;
        self.reward_at_assign(vi);
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
        #[cfg(feature = "best_phases_tracking")]
        if self.root_level == lv {
            // self.check_best_phase(vi);
            self.make_var_asserted(vi);
        }
    }
    fn assign_by_decision(&mut self, l: Lit) {
        debug_assert!(l.vi() < self.var.len());
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(
            !self.trail.contains(&!l),
            "asg.trail contains a strange literal",
        );
        self.level_up();
        let dl = self.trail_lim.len() as DecisionLevel;
        let vi = l.vi();
        self.level[vi] = dl;
        let v = &mut self.var[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        set_assign!(self, l);
        self.reason[vi] = AssignReason::default();
        self.reward_at_assign(vi);
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
        self.num_decision += 1;
    }
    fn assign_by_unitclause(&mut self, l: Lit) {
        self.cancel_until(self.root_level);
        debug_assert!(self.trail.iter().all(|k| k.vi() != l.vi()));
        let vi = l.vi();
        self.level[vi] = self.root_level;
        set_assign!(self, l);
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
        // NOTE: synchronize the following with handle(SolverEvent::Assert)
        self.make_var_asserted(vi);
    }
    fn cancel_until(&mut self, lv: DecisionLevel) {
        if self.trail_lim.len() as u32 <= lv {
            return;
        }
        if self.best_assign {
            self.save_best_phases();
            self.best_assign = false;
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
        // assert!(lim < self.q_head) doesn't hold sometimes in chronoBT.
        self.q_head = self.q_head.min(lim);
        if lv == self.root_level {
            self.num_restart += 1;
            self.cpr_ema.update(self.num_conflict);
            self.num_asserted_vars = self.stack_len();
        }
    }
    fn backtrack_sandbox(&mut self) {
        let lim = self.trail_lim[self.root_level as usize];
        for i in lim..self.trail.len() {
            let l = self.trail[i];
            let vi = l.vi();
            let v = &mut self.var[vi];
            v.set(Flag::PHASE, var_assign!(self, vi).unwrap());
            unset_assign!(self, vi);
            self.reason[vi] = AssignReason::default();
            self.insert_heap(vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(self.root_level as usize);
        self.q_head = self.q_head.min(lim);
    }
    /// UNIT PROPAGATION.
    /// Note:
    ///  - *Precondition*: no checking dead clauses. They cause crash.
    ///  - This function assumes there's no dead clause.
    ///    So Eliminator should call `garbage_collect` before me.
    ///  - The order of literals in binary clauses will be modified to hold
    ///    propagation order.
    fn propagate<C>(&mut self, cdb: &mut C) -> ClauseId
    where
        C: ClauseDBIF,
    {
        let bin_watcher = cdb.bin_watcher_lists() as *const [Vec<Watch>];
        let watcher = cdb.watcher_lists_mut() as *mut [Vec<Watch>];
        unsafe {
            while let Some(p) = self.trail.get(self.q_head) {
                self.num_propagation += 1;
                self.q_head += 1;
                let sweeping = usize::from(*p);
                let false_lit = !*p;
                // we have to drop `p` here to use self as a mutable reference again later.

                //
                //## binary loop
                //
                let bin_source = (*bin_watcher).get_unchecked(sweeping);
                for w in bin_source.iter() {
                    debug_assert!(!cdb[w.c].is(Flag::DEAD));
                    debug_assert!(!self.var[w.blocker.vi()].is(Flag::ELIMINATED));
                    debug_assert_ne!(w.blocker, false_lit);

                    #[cfg(feature = "boundary_check")]
                    debug_assert_eq!(cdb[w.c].len(), 2);

                    match lit_assign!(self, w.blocker) {
                        Some(true) => (),
                        Some(false) => {
                            self.num_conflict += 1;
                            self.dpc_ema.update(self.num_decision);
                            self.ppc_ema.update(self.num_propagation);
                            return w.c;
                        }
                        None => {
                            // self.reward_at_propagation(false_lit.vi());
                            assert!(!self.var[w.blocker.vi()].is(Flag::ELIMINATED));
                            self.assign_by_implication(
                                w.blocker,
                                AssignReason::Implication(w.c, false_lit),
                                *self.level.get_unchecked(false_lit.vi()),
                            );
                        }
                    }
                }
                //
                //## normal clause loop
                //
                let source = (*watcher).get_unchecked_mut(sweeping);
                let mut n = 0;
                'next_clause: while n < source.len() {
                    let w = source.get_unchecked_mut(n);
                    n += 1;
                    assert!(!self.var[w.blocker.vi()].is(Flag::ELIMINATED));
                    assert_ne!(w.blocker.vi(), false_lit.vi());
                    assert!(w.blocker == cdb[w.c].lits[0] || w.blocker == cdb[w.c].lits[1]);

                    let other_watch = w.blocker;
                    let other_watch_value = lit_assign!(self, other_watch);
                    if let Some(true) = other_watch_value {
                        // In this path, we use only `AssignStack::assign`.
                        // assert!(w.blocker == cdb[w.c].lits[0] || w.blocker == cdb[w.c].lits[1]);
                        continue 'next_clause;
                    }
                    debug_assert!(!cdb[w.c].is(Flag::DEAD));
                    // cdb.watches(w.c);

                    let Clause {
                        ref mut lits,
                        ref mut search_from,
                        ..
                    } = cdb[w.c];
                    debug_assert!(lits[0] == false_lit || lits[1] == false_lit);

                    // if lits[0] == false_lit {
                    //     lits.swap(0, 1);
                    // }
                    let other_watch_pos = (lits[1] == w.blocker) as usize;

                    // assert_ne!(lit_assign!(self, lits[0]), Some(false));

                    //## Search an un-falsified literal
                    //
                    let len = lits.len();
                    // Gathering good literals at the beginning of lits.
                    // for k in (*search_from..len).chain(2..*search_from) {
                    let mut k = 2;
                    while k < len {
                        let lk = *lits.get_unchecked(k);
                        if lit_assign!(self, lk) != Some(false) {
                            let cid = w.c;
                            // if lit_assign!(self, lits[0]) == Some(false) {
                            //     dbg!((w.c, &lits, false_lit));
                            //     for l in lits.iter() {
                            //         if let Some(pos) = self.trail.iter().position(|m| m.vi() == l.vi()) {
                            //             if self.q_head < pos {
                            //                 println!(" - {:>10} unchecked assign", l);
                            //             } else {
                            //                 println!(" - {:>10} checked assign", l);
                            //             }
                            //         } else {
                            //             println!(" - {:>10} unassigned", l);
                            //         }
                            //     }
                            // }
                            // assert_ne!(lit_assign!(self, lits[0]), Some(false));
                            (*watcher)
                                .get_unchecked_mut(usize::from(!other_watch))
                                .update_blocker(cid, lk)
                                .unwrap();
                            n -= 1;
                            let mut w = source.detach(n);
                            w.blocker = other_watch;
                            // assert_ne!(*lk, w.blocker);
                            (*watcher).get_unchecked_mut(usize::from(!lk)).register(w);
                            lits.swap(1 - other_watch_pos, k);

                            // If `search_from` gets out of range,
                            // the next loop will ignore it safely;
                            // the first iteration loop becomes null.
                            *search_from = k + 1;
                            cdb.watches(cid);
                            continue 'next_clause;
                        }
                        k += 1;
                    }
                    if lits[0] == false_lit {
                        lits.swap(0, 1);
                    }
                    if other_watch_value == Some(false) {
                        let cid = w.c;
                        self.num_conflict += 1;
                        self.dpc_ema.update(self.num_decision);
                        self.ppc_ema.update(self.num_propagation);
                        return cid;
                    }
                    let lv = lits[1..]
                        .iter()
                        .map(|l| self.level[l.vi()])
                        .max()
                        .unwrap_or(self.root_level);
                    // self.reward_at_propagation(false_lit.vi());
                    self.assign_by_implication(
                        other_watch,
                        AssignReason::Implication(w.c, NULL_LIT),
                        lv,
                    );
                }
            }
        }
        let na = self.q_head + self.num_eliminated_vars;
        if self.num_best_assign <= na && 0 < self.decision_level() {
            self.best_assign = true;
            self.num_best_assign = na;
        }
        ClauseId::default()
    }
    //
    //## How to generate propagate_sandbox from propagate
    //
    // 1. copy it
    // 1. delete codes about reward
    // 1. delete codes about best-phases
    // 1. delete codes about search_from
    // 1. delete codes about stats: num_*, ema_*
    // 1. delete comments
    //
    fn propagate_sandbox<C>(&mut self, cdb: &mut C) -> ClauseId
    where
        C: ClauseDBIF,
    {
        let bin_watcher = cdb.bin_watcher_lists() as *const [Vec<Watch>];
        let watcher = cdb.watcher_lists_mut() as *mut [Vec<Watch>];
        unsafe {
            while let Some(p) = self.trail.get(self.q_head) {
                self.q_head += 1;
                let sweeping = usize::from(*p);
                let false_lit = !*p;

                //
                //## binary loop
                //
                let bin_source = (*bin_watcher).get_unchecked(sweeping);
                for w in bin_source.iter() {
                    debug_assert!(!cdb[w.c].is(Flag::DEAD));
                    debug_assert!(!self.var[w.blocker.vi()].is(Flag::ELIMINATED));
                    debug_assert_ne!(w.blocker, false_lit);

                    #[cfg(feature = "boundary_check")]
                    debug_assert_eq!(cdb[w.c].len(), 2);

                    match lit_assign!(self, w.blocker) {
                        Some(true) => (),
                        Some(false) => {
                            return w.c;
                        }
                        None => {
                            assert!(!self.var[w.blocker.vi()].is(Flag::ELIMINATED));
                            self.assign_by_implication(
                                w.blocker,
                                AssignReason::Implication(w.c, false_lit),
                                *self.level.get_unchecked(false_lit.vi()),
                            );
                        }
                    }
                }
                //
                //## normal clause loop
                //
                let source = (*watcher).get_unchecked_mut(sweeping);
                let mut n = 0;
                'next_clause: while n < source.len() {
                    let w = source.get_unchecked_mut(n);
                    n += 1;
                    assert!(!self.var[w.blocker.vi()].is(Flag::ELIMINATED));
                    assert_ne!(w.blocker.vi(), false_lit.vi());
                    assert!(w.blocker == cdb[w.c].lits[0] || w.blocker == cdb[w.c].lits[1]);

                    let other_watch = w.blocker;
                    let other_watch_value = lit_assign!(self, other_watch);
                    if let Some(true) = other_watch_value {
                        continue 'next_clause;
                    }
                    assert!(!cdb[w.c].is(Flag::DEAD));
                    let Clause { ref mut lits, .. } = cdb[w.c];
                    assert!(lits[0] == false_lit || lits[1] == false_lit);
                    let other_watch_pos = (lits[1] == w.blocker) as usize;
                    // assert_ne!(lit_assign!(self, lits[0]), Some(false));

                    //## Search an un-falsified literal
                    //
                    let len = lits.len();
                    // Gathering good literals at the beginning of lits.
                    // for k in (*search_from..len).chain(2..*search_from) {
                    let mut k = 2;
                    while k < len {
                        let lk = *lits.get_unchecked(k);
                        if lit_assign!(self, lk) != Some(false) {
                            let cid = w.c;
                            (*watcher)
                                .get_unchecked_mut(usize::from(!other_watch))
                                .update_blocker(cid, lk)
                                .unwrap();
                            n -= 1;
                            let mut w = source.detach(n);
                            w.blocker = other_watch;
                            (*watcher).get_unchecked_mut(usize::from(!lk)).register(w);
                            lits.swap(1 - other_watch_pos, k);
                            cdb.watches(cid);
                            continue 'next_clause;
                        }
                        k += 1;
                    }
                    if lits[0] == false_lit {
                        lits.swap(0, 1);
                    }
                    if other_watch_value == Some(false) {
                        let cid = w.c;
                        return cid;
                    }
                    let lv = lits[1..]
                        .iter()
                        .map(|l| self.level[l.vi()])
                        .max()
                        .unwrap_or(self.root_level);
                    self.assign_by_implication(
                        other_watch,
                        AssignReason::Implication(w.c, NULL_LIT),
                        lv,
                    );
                }
            }
        }
        ClauseId::default()
    }
}

impl AssignStack {
    /// check usability of the saved best phase.
    /// return `true` if the current best phase got invalid.
    #[cfg(not(feature = "best_phases_tracking"))]
    pub fn check_best_phase(&mut self, _: VarId) -> bool {
        false
    }
    #[cfg(feature = "best_phases_tracking")]
    pub fn check_best_phase(&mut self, vi: VarId) -> bool {
        if let Some((b, _)) = self.best_phases.get(&vi) {
            debug_assert!(self.assign[vi].is_some());
            if self.assign[vi] != Some(*b) {
                if self.root_level == self.level[vi] {
                    self.best_phases.clear();
                    self.num_best_assign = self.num_eliminated_vars;
                }
                return true;
            }
        }
        false
    }
    fn level_up(&mut self) {
        self.trail_lim.push(self.trail.len());
    }
    /// save the current assignments as the best phases
    fn save_best_phases(&mut self) {
        #[cfg(feature = "best_phases_tracking")]
        for l in self.trail.iter().skip(self.len_upto(self.root_level)) {
            let vi = l.vi();
            if let Some(b) = self.assign[vi] {
                self.best_phases.insert(vi, (b, self.reason[vi]));
            }
        }
        self.build_best_at = self.num_propagation;
        #[cfg(feature = "rephase")]
        {
            self.phase_age = 0;
        }
    }
}

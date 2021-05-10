/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{AssignIF, AssignStack, VarHeapIF},
    crate::{cdb::ClauseDBIF, types::*},
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

#[cfg(feature = "unsafe_access")]
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
    };
}
#[cfg(not(feature = "unsafe_access"))]
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        $asg.assign[$var]
    };
}

#[cfg(feature = "unsafe_access")]
macro_rules! lit_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l => match unsafe { *$asg.assign.get_unchecked(l.vi()) } {
                Some(x) if !bool::from(l) => Some(!x),
                x => x,
            },
        }
    };
}
#[cfg(not(feature = "unsafe_access"))]
macro_rules! lit_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l => match $asg.assign[l.vi()] {
                Some(x) if !bool::from(l) => Some(!x),
                x => x,
            },
        }
    };
}

#[cfg(feature = "unsafe_access")]
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
#[cfg(not(feature = "unsafe_access"))]
macro_rules! set_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l => {
                let vi = l.vi();
                $asg.assign[vi] = Some(bool::from(l));
            }
        }
    };
}

macro_rules! unset_assign {
    ($asg: expr, $var: expr) => {
        $asg.assign[$var] = None;
    };
}

impl PropagateIF for AssignStack {
    fn assign_at_root_level(&mut self, l: Lit) -> MaybeInconsistent {
        self.cancel_until(self.root_level);
        let vi = l.vi();
        debug_assert!(vi < self.var.len());
        debug_assert!(!self.var[vi].is(Flag::ELIMINATED));
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
            _ => Err(SolverError::RootLevelConflict(ClauseId::from(l))),
        }
    }
    fn assign_by_implication(&mut self, l: Lit, reason: AssignReason, lv: DecisionLevel) {
        debug_assert!(usize::from(l) != 0, "Null literal is about to be enqueued");
        debug_assert!(l.vi() < self.var.len());
        // The following doesn't hold anymore by using chronoBT.
        // assert!(self.trail_lim.is_empty() || !cid.is_none());
        let vi = l.vi();
        debug_assert!(!self.var[vi].is(Flag::ELIMINATED));
        assert!(var_assign!(self, vi) == Some(bool::from(l)) || var_assign!(self, vi).is_none());
        set_assign!(self, l);
        self.level[vi] = lv;
        self.reason[vi] = reason;
        self.reward_at_assign(vi);
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
        if self.root_level == lv {
            self.make_var_asserted(vi);
        }
    }
    fn assign_by_decision(&mut self, l: Lit) {
        assert!(
            var_assign!(self, l.vi()) == Some(bool::from(l)) || var_assign!(self, l.vi()).is_none()
        );
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
        self.trail.push(l);
        self.num_decision += 1;
        assert!(self.q_head < self.trail.len());
    }
    fn assign_by_unitclause(&mut self, l: Lit) {
        self.cancel_until(self.root_level);
        assert!(
            var_assign!(self, l.vi()) == Some(bool::from(l)) || var_assign!(self, l.vi()).is_none()
        );
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
        // We assume that backtrack is never happened in level zero.
        let lim = self.trail_lim[lv as usize];
        let mut ooo_propagated: Vec<Lit> = Vec::new();
        let mut ooo_unpropagated: Vec<Lit> = Vec::new();
        for i in lim..self.trail.len() {
            let l = self.trail[i];
            assert!(
                self.assign[l.vi()].is_some(),
                "cancel_until found unassigned var in trail {}{:?}",
                l.vi(),
                &self.var[l.vi()],
            );
            let vi = l.vi();
            assert!(self.q_head <= i || self.var[vi].is(Flag::PROPAGATED),
                    "unpropagated assigned level-{} var {:?},{:?} (loc:{} in trail{:?}) found, staying at level {}",
                    self.level[vi],
                    self.var[vi],
                    self.reason[vi],
                    i,
                    self.trail_lim.iter().filter(|n| **n <= i).collect::<Vec<_>>(),
                    self.decision_level(),
            );
            if self.level[vi] <= lv {
                if i < self.q_head {
                    ooo_propagated.push(l);
                } else {
                    ooo_unpropagated.push(l);
                }
                continue;
            }
            let v = &mut self.var[vi];
            v.turn_off(Flag::PROPAGATED);
            v.set(Flag::PHASE, var_assign!(self, vi).unwrap());
            unset_assign!(self, vi);
            self.reason[vi] = AssignReason::default();
            self.reward_at_unassign(vi);
            self.insert_heap(vi);
        }
        self.trail.truncate(lim);
        self.trail.append(&mut ooo_propagated);
        // || for l in self.trail.iter() {
        // ||     assert!(
        // ||         self.var[l.vi()].is(Flag::PROPAGATED),
        // ||         "unpropagated {}: {:?}",
        // ||         *l,
        // ||         &self.var[l.vi()],
        // ||     );
        // || }

        // || assert!(self
        // ||     .trail
        // ||     .iter()
        // ||     .all(|l| self.var[l.vi()].is(Flag::PROPAGATED)));
        self.q_head = self.trail.len();
        self.trail.append(&mut ooo_unpropagated);
        debug_assert!(self
            .trail
            .iter()
            .all(|l| var_assign!(self, l.vi()).is_some()));
        debug_assert!(self.trail.iter().all(|k| !self.trail.contains(&!*k)));
        self.trail_lim.truncate(lv as usize);
        // assert!(lim < self.q_head) doesn't hold sometimes in chronoBT.
        // ||  self.q_head = self.q_head.min(lim);
        if lv == self.root_level {
            // || assert!(self
            // ||     .trail
            // ||     .iter()
            // ||     .take(self.q_head)
            // ||     .all(|l| self.level[l.vi()] == self.root_level
            // ||         && self.var[l.vi()].is(Flag::PROPAGATED)));
            // self.trail.clear();
            // self.trail.append(&mut ooo_unpropagated);
            // self.q_head = 0;
            self.num_restart += 1;
            self.cpr_ema.update(self.num_conflict);
        }

        assert!(self.q_head == 0 || self.assign[self.trail[self.q_head - 1].vi()].is_some());
        assert!(
            self.q_head == 0 || self.var[self.trail[self.q_head - 1].vi()].is(Flag::PROPAGATED)
        );
    }
    fn backtrack_sandbox(&mut self) {
        if self.trail_lim.is_empty() {
            return;
        }
        let lim = self.trail_lim[self.root_level as usize];
        for i in lim..self.trail.len() {
            let l = self.trail[i];
            let vi = l.vi();
            assert!(self.root_level < self.level[vi]);
            let v = &mut self.var[vi];
            v.set(Flag::PHASE, var_assign!(self, vi).unwrap());
            unset_assign!(self, vi);
            self.reason[vi] = AssignReason::default();
            self.insert_heap(vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(self.root_level as usize);
        self.q_head = self.trail.len();
        // self.trail.clear();
        // self.trail_lim.clear();
        // self.q_head = 0;
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
        if self.decision_level() == self.root_level && !self.trail.is_empty() {
            if let Some(cc) = self.propagate_at_root_level(cdb) {
                return cc;
            }
        }
        while let Some(p) = self.trail.get(self.q_head) {
            self.num_propagation += 1;
            self.q_head += 1;
            assert!(!self.var[p.vi()].is(Flag::PROPAGATED));
            self.var[p.vi()].turn_on(Flag::PROPAGATED);
            let sweeping = Lit::from(usize::from(*p));
            let false_lit = !*p;

            // we have to drop `p` here to use self as a mutable reference again later.
            //
            //## binary loop
            //
            let bi_clause = cdb.bi_clause_map(*p);
            // // let mut conflicting_cid: ClauseId = ClauseId::default();
            // // let mut conflicting_act: f64 = 0.0;
            for (&blocker, &cid) in bi_clause.iter() {
                debug_assert!(!cdb[cid].is_dead());
                assert!(!self.var[blocker.vi()].is(Flag::ELIMINATED));
                debug_assert_ne!(blocker, false_lit);
                #[cfg(feature = "boundary_check")]
                debug_assert_eq!(cdb[cid].len(), 2);
                match lit_assign!(self, blocker) {
                    Some(true) => (),
                    Some(false) => {
                        self.dpc_ema.update(self.num_decision);
                        self.ppc_ema.update(self.num_propagation);
                        self.num_conflict += 1;
                        return cid;
                        // // let act = self.var[blocker.vi()].activity();
                        // // if conflicting_act < act {
                        // //     conflicting_act = act;
                        // //     conflicting_cid = cid;
                        // // }
                    }
                    None => {
                        self.assign_by_implication(
                            blocker,
                            AssignReason::Implication(cid, false_lit),
                            self.level[false_lit.vi()],
                        );
                    }
                }
            }
            // // if conflicting_cid != ClauseId::default() {
            // //     self.dpc_ema.update(self.num_decision);
            // //     self.ppc_ema.update(self.num_propagation);
            // //     self.num_conflict += 1;
            // //     return conflicting_cid;
            // // }
            //
            //## normal clause loop
            //
            let source = cdb.detach_watch_cache(sweeping);
            let mut watches = source.iter();
            'next_clause: while let Some((cid, other_watch)) = watches.next().deref_watch() {
                assert!(!self.var[other_watch.vi()].is(Flag::ELIMINATED));
                // assert_ne!(other_watch.vi(), false_lit.vi());
                // assert!(other_watch == cdb[cid].lit0() || other_watch == cdb[cid].lit1());
                let other_watch_value = lit_assign!(self, other_watch);
                if let Some(true) = other_watch_value {
                    debug_assert!(!self.var[other_watch.vi()].is(Flag::ELIMINATED));
                    // In this path, we use only `AssignStack::assign`.
                    // assert!(w.blocker == cdb[w.c].lits[0] || w.blocker == cdb[w.c].lits[1]);
                    cdb.reregister_watch_cache(sweeping, Some((cid, other_watch)));
                    continue 'next_clause;
                }
                assert!(
                    !cdb[cid].is_dead(),
                    "dead clause {}{} found during propagating {}",
                    cid,
                    &cdb[cid],
                    false_lit,
                );
                let c = &mut cdb[cid];

                #[cfg(not(feature = "maintain_watch_cache"))]
                let other_watch = if false_lit == c.lit0() && other_watch != c.lit1() {
                    c.lit1()
                } else if false_lit == c.lit1() && other_watch != c.lit0() {
                    c.lit0()
                } else {
                    other_watch
                };
                #[cfg(not(feature = "maintain_watch_cache"))]
                let other_watch_value = lit_assign!(self, other_watch);
                #[cfg(not(feature = "maintain_watch_cache"))]
                if let Some(true) = other_watch_value {
                    debug_assert!(!self.var[other_watch.vi()].is(Flag::ELIMINATED));
                    // In this path, we use only `AssignStack::assign`.
                    // assert!(w.blocker == cdb[w.c].lits[0] || w.blocker == cdb[w.c].lits[1]);
                    cdb.reregister_watch_cache(sweeping, Some((cid, other_watch)));
                    continue 'next_clause;
                }

                debug_assert!(c.lit0() == false_lit || c.lit1() == false_lit);
                let false_watch_pos = (c.lit0() == other_watch) as usize;
                //
                //## Search an un-falsified literal
                //
                // Gathering good literals at the beginning of lits.
                for (k, lk) in c.iter().enumerate().skip(2) {
                    if lit_assign!(self, *lk) != Some(false) {
                        cdb.update_watch_cache(cid, false_watch_pos, k, true);
                        continue 'next_clause;
                    }
                }
                if false_watch_pos == 0 {
                    cdb.swap_watch(cid);
                }
                cdb.reregister_watch_cache(sweeping, Some((cid, other_watch)));
                if other_watch_value == Some(false) {
                    self.num_conflict += 1;
                    self.dpc_ema.update(self.num_decision);
                    self.ppc_ema.update(self.num_propagation);
                    while cdb.reregister_watch_cache(sweeping, watches.next().deref_watch()) {}
                    return cid;
                }
                let lv = cdb[cid]
                    .iter()
                    .skip(1)
                    .map(|l| self.level[l.vi()])
                    .max()
                    .unwrap_or(self.root_level);
                self.assign_by_implication(
                    other_watch,
                    AssignReason::Implication(cid, NULL_LIT),
                    lv,
                );
            }
        }
        // wipe asserted literals from trail and increment the number of asserted vars.
        if self.decision_level() == self.root_level && !self.trail.is_empty() {
            self.num_asserted_vars += self.trail.len();
            self.trail.clear();
            self.q_head = 0;
        }
        let na = self.q_head + self.num_eliminated_vars + self.num_asserted_vars;
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
    // 1. (allow dead clauses)
    // 1. (allow eliminated vars)
    //
    fn propagate_sandbox<C>(&mut self, cdb: &mut C) -> ClauseId
    where
        C: ClauseDBIF,
    {
        while let Some(p) = self.trail.get(self.q_head) {
            self.q_head += 1;
            let sweeping = Lit::from(usize::from(*p));
            let false_lit = !*p;
            let bi_clause = cdb.bi_clause_map(*p);
            for (&blocker, &cid) in bi_clause.iter() {
                if cdb[cid].is_dead() {
                    continue;
                }
                debug_assert!(!cdb[cid].is_dead());
                debug_assert!(!self.var[blocker.vi()].is(Flag::ELIMINATED));
                debug_assert_ne!(blocker, false_lit);
                #[cfg(feature = "boundary_check")]
                debug_assert_eq!(cdb[cid].len(), 2);
                match lit_assign!(self, blocker) {
                    Some(true) => (),
                    Some(false) => {
                        assert!(!cdb[cid].is_dead());
                        return cid;
                    }
                    None => {
                        self.assign_by_implication(
                            blocker,
                            AssignReason::Implication(cid, false_lit),
                            self.level[false_lit.vi()],
                        );
                    }
                }
            }
            let source = cdb.detach_watch_cache(sweeping);
            let mut watches = source.iter();
            'next_clause: while let Some((cid, other_watch)) = watches.next().deref_watch() {
                if cdb[cid].is_dead() {
                    continue 'next_clause;
                }
                let other_watch_value = lit_assign!(self, other_watch);
                if let Some(true) = other_watch_value {
                    assert!(!self.var[other_watch.vi()].is(Flag::ELIMINATED));
                    cdb.reregister_watch_cache(sweeping, Some((cid, other_watch)));
                    continue 'next_clause;
                }
                debug_assert!(!cdb[cid].is_dead());
                let c = &mut cdb[cid];
                #[cfg(not(feature = "maintain_watch_cache"))]
                let other_watch = if false_lit == c.lit0() && other_watch != c.lit1() {
                    c.lit1()
                } else if false_lit == c.lit1() && other_watch != c.lit0() {
                    c.lit0()
                } else {
                    other_watch
                };
                #[cfg(not(feature = "maintain_watch_cache"))]
                let other_watch_value = lit_assign!(self, other_watch);
                #[cfg(not(feature = "maintain_watch_cache"))]
                if let Some(true) = other_watch_value {
                    assert!(!self.var[other_watch.vi()].is(Flag::ELIMINATED));
                    cdb.reregister_watch_cache(sweeping, Some((cid, other_watch)));
                    // cdb.watches(cid, &format!("\npropagate {} at L545", false_lit));
                    continue 'next_clause;
                }
                debug_assert!(c.lit0() == false_lit || c.lit1() == false_lit);
                let false_watch_pos = (c.lit0() == other_watch) as usize;
                for (k, lk) in c.iter().enumerate().skip(2) {
                    if lit_assign!(self, *lk) != Some(false) {
                        cdb.update_watch_cache(cid, false_watch_pos, k, true);
                        continue 'next_clause;
                    }
                }
                if false_watch_pos == 0 {
                    cdb.swap_watch(cid);
                }
                cdb.reregister_watch_cache(sweeping, Some((cid, other_watch)));
                if other_watch_value == Some(false) {
                    while cdb.reregister_watch_cache(sweeping, watches.next().deref_watch()) {}
                    assert!(!cdb[cid].is_dead());
                    // cdb.watches(cid, "propagate543");
                    return cid;
                }
                let lv = cdb[cid]
                    .iter()
                    .skip(1)
                    .map(|l| self.level[l.vi()])
                    .max()
                    .unwrap_or(self.root_level);
                self.assign_by_implication(
                    other_watch,
                    AssignReason::Implication(cid, NULL_LIT),
                    lv,
                );
            }
        }
        ClauseId::default()
    }
}

impl AssignStack {
    ///
    fn propagate_at_root_level<C>(&mut self, cdb: &mut C) -> Option<ClauseId>
    where
        C: ClauseDBIF,
    {
        let mut num_propagated = 0;
        while num_propagated < self.trail.len() {
            num_propagated = self.trail.len();
            for ci in 1..cdb.len() {
                let cid = ClauseId::from(ci);
                if cdb[cid].is_dead() {
                    continue;
                }
                assert!(cdb[cid]
                    .iter()
                    .all(|l| !self.var[l.vi()].is(Flag::ELIMINATED)));
                match cdb.transform_by_simplification(self, cid) {
                    RefClause::Clause(_) => (),
                    RefClause::Dead => (),
                    RefClause::EmptyClause => return Some(cid),
                    RefClause::RegisteredClause(_) => (),
                    RefClause::UnitClause(lit) => {
                        cdb.certificate_add_assertion(lit);
                        if self.assign_at_root_level(lit).is_err() {
                            return Some(cid);
                        } else {
                            cdb.remove_clause(cid);
                        }
                    }
                }
            }
        }
        // for l in self.trail.iter() {
        //     self.var[l.vi()].turn_on(Flag::PROPAGATED);
        // }
        None
    }

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
                    self.num_best_assign = self.num_asserted_vars + self.num_eliminated_vars;
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
        {
            self.best_phases.clear();
            for l in self.trail.iter().skip(self.len_upto(self.root_level)) {
                let vi = l.vi();
                if let Some(b) = self.assign[vi] {
                    self.best_phases.insert(vi, (b, self.reason[vi]));
                }
            }
        }
        self.build_best_at = self.num_propagation;
        #[cfg(feature = "rephase")]
        {
            self.phase_age = 0;
        }
    }
}

trait WatchCacheAdapter {
    fn deref_watch(self) -> Option<(ClauseId, Lit)>;
}

impl WatchCacheAdapter for Option<(&ClauseId, &Lit)> {
    fn deref_watch(self) -> Option<(ClauseId, Lit)> {
        self.map(|(c, i)| (*c, *i))
    }
}

impl WatchCacheAdapter for Option<&(ClauseId, Lit)> {
    fn deref_watch(self) -> Option<(ClauseId, Lit)> {
        self.map(|(c, i)| (*c, *i))
    }
}

/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{AssignIF, AssignStack, VarHeapIF, VarManipulateIF},
    crate::{cdb::ClauseDBIF, types::*},
};

/// API for Boolean Constraint Propagation like [`propagate`](`crate::assign::PropagateIF::propagate`), [`assign_by_decision`](`crate::assign::PropagateIF::assign_by_decision`), [`cancel_until`](`crate::assign::PropagateIF::cancel_until`), and so on.
pub trait PropagateIF {
    /// add an assignment at root level as a precondition.
    ///
    /// # Errors
    ///
    /// emit `SolverError::Inconsistent` exception if solver becomes inconsistent.
    fn assign_at_root_level(&mut self, l: Lit) -> MaybeInconsistent;
    /// unsafe enqueue (assign by implication); doesn't emit an exception.
    ///
    /// ## Warning
    /// Callers must assure the consistency after this assignment.
    fn assign_by_implication(&mut self, l: Lit, lv: DecisionLevel, cid: ClauseId, by: Option<Lit>);
    /// unsafe assume (assign by decision); doesn't emit an exception.
    /// ## Caveat
    /// Callers have to assure the consistency after this assignment.
    fn assign_by_decision(&mut self, l: Lit);
    /// execute *backjump*.
    fn cancel_until(&mut self, lv: DecisionLevel);
    /// execute backjump in vivification sandbox
    fn backtrack_sandbox(&mut self);
    /// execute *boolean constraint propagation* or *unit propagation*.
    fn propagate<C>(&mut self, cdb: &mut C) -> Option<ClauseId>
    where
        C: ClauseDBIF;
    /// `propagate` for vivification, which allows dead clauses.
    fn propagate_sandbox<C>(&mut self, cdb: &mut C) -> Option<ClauseId>
    where
        C: ClauseDBIF;
    /// propagate then clear asserted literals
    fn clear_asserted_literals<C>(&mut self, cdb: &mut C) -> MaybeInconsistent
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
                self.reason[vi] = AssignReason::Asserted(self.num_conflict);
                debug_assert!(!self.trail.contains(&!l));
                self.trail.push(l);
                self.make_var_asserted(vi);
                Ok(())
            }
            Some(x) if x == bool::from(l) => {
                #[cfg(feature = "boundary_check")]
                panic!("double assginment(assertion)");
                #[cfg(not(feature = "boundary_check"))]
                // Vivification tries to assign a var by propagation then can assert it.
                // To make sure the var is asserted, we need to nullify its reason.
                // || self.reason[vi] = AssignReason::None;
                // self.make_var_asserted(vi);
                Ok(())
            }
            _ => Err(SolverError::RootLevelConflict(Some(ClauseId::from(l)))),
        }
    }
    fn assign_by_implication(&mut self, l: Lit, lv: DecisionLevel, cid: ClauseId, by: Option<Lit>) {
        debug_assert!(usize::from(l) != 0, "Null literal is about to be enqueued");
        debug_assert!(l.vi() < self.var.len());
        // The following doesn't hold anymore by using chronoBT.
        // assert!(self.trail_lim.is_empty() || !cid.is_none());
        let vi = l.vi();
        debug_assert!(!self.var[vi].is(Flag::ELIMINATED));
        debug_assert!(
            var_assign!(self, vi) == Some(bool::from(l)) || var_assign!(self, vi).is_none()
        );
        debug_assert_eq!(self.assign[vi], None);
        debug_assert_eq!(self.reason[vi], AssignReason::None);
        debug_assert!(self.trail.iter().all(|rl| *rl != l));
        set_assign!(self, l);
        self.level[vi] = lv;
        self.reason[vi] = AssignReason::Implication(cid, by.unwrap_or(NULL_LIT));
        self.reward_at_assign(vi);
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
        if self.root_level == lv {
            self.make_var_asserted(vi);
        }

        #[cfg(feature = "boundary_check")]
        {
            self.var[vi].propagated_at = self.num_conflict;
            self.var[vi].state = VarState::Assigned(self.num_conflict);
        }
    }
    fn assign_by_decision(&mut self, l: Lit) {
        debug_assert!(
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
        debug_assert_eq!(self.assign[vi], None);
        debug_assert_eq!(self.reason[vi], AssignReason::None);
        set_assign!(self, l);
        self.reason[vi] = AssignReason::Decision(self.decision_level());
        self.reward_at_assign(vi);
        self.trail.push(l);
        self.num_decision += 1;
        debug_assert!(self.q_head < self.trail.len());
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
        let mut unpropagated: Vec<Lit> = Vec::new();
        for i in lim..self.trail.len() {
            let l = self.trail[i];
            debug_assert!(
                self.assign[l.vi()].is_some(),
                "cancel_until found unassigned var in trail {}{:?}",
                l.vi(),
                &self.var[l.vi()],
            );
            let vi = l.vi();
            #[cfg(feature = "debug_propagation")]
            debug_assert!(self.q_head <= i || self.var[vi].is(Flag::PROPAGATED),
                    "unpropagated assigned level-{} var {:?},{:?} (loc:{} in trail{:?}) found, staying at level {}",
                    self.level[vi],
                    self.var[vi],
                    self.reason[vi],
                    i,
                    self.trail_lim.iter().filter(|n| **n <= i).collect::<Vec<_>>(),
                    self.decision_level(),
            );
            if self.level[vi] <= lv {
                unpropagated.push(l);
                continue;
            }
            let v = &mut self.var[vi];
            #[cfg(feature = "debug_propagation")]
            v.turn_off(Flag::PROPAGATED);
            v.set(Flag::PHASE, var_assign!(self, vi).unwrap());

            #[cfg(feature = "boundary_check")]
            {
                v.propagated_at = self.num_conflict;
                v.state = VarState::Unassigned(self.num_conflict);
            }

            unset_assign!(self, vi);
            self.reason[vi] = AssignReason::None;
            self.reward_at_unassign(vi);
            self.insert_heap(vi);
        }
        self.trail.truncate(lim);
        // moved below -- self.q_head = self.trail.len();
        // see https://github.com/shnarazk/splr/issues/117
        self.q_head = self.trail.len().min(self.q_head);
        self.trail.append(&mut unpropagated);
        debug_assert!(self
            .trail
            .iter()
            .all(|l| var_assign!(self, l.vi()).is_some()));
        debug_assert!(self.trail.iter().all(|k| !self.trail.contains(&!*k)));
        self.trail_lim.truncate(lv as usize);
        // assert!(lim < self.q_head) doesn't hold sometimes in chronoBT.
        if lv == self.root_level {
            self.num_restart += 1;
            self.cpr_ema.update(self.num_conflict);
        }

        debug_assert!(self.q_head == 0 || self.assign[self.trail[self.q_head - 1].vi()].is_some());
        #[cfg(feature = "debug_propagation")]
        debug_assert!(
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
            debug_assert!(self.root_level < self.level[vi]);
            let v = &mut self.var[vi];
            v.set(Flag::PHASE, var_assign!(self, vi).unwrap());
            unset_assign!(self, vi);
            self.reason[vi] = AssignReason::None;
            self.insert_heap(vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(self.root_level as usize);
        self.q_head = self.trail.len();
    }
    /// UNIT PROPAGATION.
    /// Note:
    ///  - *Precondition*: no checking dead clauses. They cause crash.
    ///  - This function assumes there's no dead clause.
    ///    So Eliminator should call `garbage_collect` before me.
    ///  - The order of literals in binary clauses will be modified to hold
    ///    propagation order.
    fn propagate<C>(&mut self, cdb: &mut C) -> Option<ClauseId>
    where
        C: ClauseDBIF,
    {
        while let Some(p) = self.trail.get(self.q_head) {
            self.num_propagation += 1;
            self.q_head += 1;
            #[cfg(feature = "debug_propagation")]
            assert!(!self.var[p.vi()].is(Flag::PROPAGATED));
            #[cfg(feature = "debug_propagation")]
            self.var[p.vi()].turn_on(Flag::PROPAGATED);
            let propagating = Lit::from(usize::from(*p));
            let false_lit = !*p;

            #[cfg(feature = "boundary_check")]
            {
                self.var[p.vi()].propagated_at = self.num_conflict;
                self.var[p.vi()].state = VarState::Propagated(self.num_conflict);
            }
            // we have to drop `p` here to use self as a mutable reference again later.

            //
            //## binary loop
            //
            // Note: bi_clause_map contains clauses themselves,
            // while the key of watch_cache is watching literals.
            // Therefore keys to access appropriate targets have the opposite phases.
            //
            for (&blocker, &cid) in cdb.bi_clause_map(false_lit).iter() {
                debug_assert!(!cdb[cid].is_dead());
                debug_assert!(!self.var[blocker.vi()].is(Flag::ELIMINATED));
                debug_assert_ne!(blocker, false_lit);

                #[cfg(feature = "boundary_check")]
                debug_assert_eq!(cdb[cid].len(), 2);

                match lit_assign!(self, blocker) {
                    Some(true) => (),
                    Some(false) => {
                        self.dpc_ema.update(self.num_decision);
                        self.ppc_ema.update(self.num_propagation);
                        self.num_conflict += 1;

                        #[cfg(feature = "boundary_check")]
                        {
                            cdb[cid].moved_at = Propagate::EmitConflict(self.num_conflict, blocker);
                        }

                        return Some(cid);
                    }
                    None => {
                        debug_assert!(cdb[cid].lit0() == false_lit || cdb[cid].lit1() == false_lit);
                        self.assign_by_implication(
                            blocker,
                            self.level[propagating.vi()],
                            cid,
                            Some(propagating),
                        );
                    }
                }
            }
            //
            //## normal clause loop
            //
            let mut source = cdb.watch_cache_iter(propagating);
            #[cfg(feature = "hashed_watch_cache")]
            let mut watches = source.iter();
            'next_clause: while let Some((cid, mut cached)) = {
                #[cfg(feature = "hashed_watch_cache")]
                {
                    watches.next().deref_watch()
                }
                #[cfg(not(feature = "hashed_watch_cache"))]
                {
                    source
                        .next()
                        .map(|index| cdb.fetch_watch_cache_entry(propagating, index))
                }
            } {
                #[cfg(feature = "boundary_check")]
                debug_assert!(
                    !cdb[cid].is_dead(),
                    "dead clause in propagation: {:?}",
                    cdb.is_garbage_collected(cid),
                );
                debug_assert!(!self.var[cached.vi()].is(Flag::ELIMINATED));
                #[cfg(feature = "maintain_watch_cache")]
                debug_assert!(
                    cached == cdb[cid].lit0() || cached == cdb[cid].lit1(),
                    "mismatch watch literal and its cache {}: l0 {}  l1 {}, timestamp: {:?}",
                    cached,
                    cdb[cid].lit0(),
                    cdb[cid].lit1(),
                    cdb[cid].timestamp(),
                );
                // assert_ne!(other_watch.vi(), false_lit.vi());
                // assert!(other_watch == cdb[cid].lit0() || other_watch == cdb[cid].lit1());
                let mut other_watch_value = lit_assign!(self, cached);
                let mut updated_cache: Option<Lit> = None;
                if Some(true) == other_watch_value {
                    #[cfg(feature = "maintain_watch_cache")]
                    debug_assert!(cdb[cid].lit0() == cached || cdb[cid].lit1() == cached);

                    // In this path, we use only `AssignStack::assign`.
                    // assert!(w.blocker == cdb[w.c].lits[0] || w.blocker == cdb[w.c].lits[1]);
                    cdb.transform_by_restoring_watch_cache(propagating, &mut source, None);

                    #[cfg(feature = "boundary_check")]
                    {
                        cdb[cid].moved_at = Propagate::CacheSatisfied(self.num_conflict);
                    }

                    continue 'next_clause;
                }
                {
                    let c = &cdb[cid];
                    let lit0 = c.lit0();
                    let lit1 = c.lit1();
                    let (false_watch_pos, other) = if false_lit == lit1 {
                        (1, lit0)
                    } else {
                        (0, lit1)
                    };

                    if cached != other {
                        cached = other;
                        other_watch_value = lit_assign!(self, other);
                        if Some(true) == other_watch_value {
                            debug_assert!(!self.var[other.vi()].is(Flag::ELIMINATED));
                            // In this path, we use only `AssignStack::assign`.
                            // assert!(w.blocker == cdb[w.c].lits[0] || w.blocker == cdb[w.c].lits[1]);
                            cdb.transform_by_restoring_watch_cache(
                                propagating,
                                &mut source,
                                Some(other),
                            );

                            #[cfg(feature = "boundary_check")]
                            {
                                cdb[cid].moved_at = Propagate::CacheSatisfied(self.num_conflict);
                            }

                            continue 'next_clause;
                        }
                        updated_cache = Some(other);
                    }
                    let c = &cdb[cid];
                    debug_assert!(lit0 == false_lit || lit1 == false_lit);
                    // let false_watch_pos = (lit1 == false_lit) as usize;
                    //
                    //## Search an un-falsified literal
                    //
                    // Gathering good literals at the beginning of lits.
                    let start = c.search_from;
                    for (k, lk) in c
                        .iter()
                        .enumerate()
                        .skip(start)
                        .chain(c.iter().enumerate().skip(2).take(start - 2))
                    {
                        if lit_assign!(self, *lk) != Some(false) {
                            let new_watch = !*lk;
                            cdb.detach_watch_cache(propagating, &mut source);
                            cdb.transform_by_updating_watch(cid, false_watch_pos, k, true);
                            cdb[cid].search_from = k + 1;
                            debug_assert!(
                                self.assigned(!new_watch) == Some(true)
                                    || self.assigned(!new_watch) == None
                            );

                            #[cfg(feature = "boundary_check")]
                            {
                                cdb[cid].moved_at = Propagate::FindNewWatch(
                                    self.num_conflict,
                                    propagating,
                                    new_watch,
                                );
                            }

                            continue 'next_clause;
                        }
                    }
                    if false_watch_pos == 0 {
                        cdb.swap_watch(cid);
                    }
                }
                // cdb.reregister_watch_cache(propagating, Some(wc_proxy));
                cdb.transform_by_restoring_watch_cache(propagating, &mut source, updated_cache);
                if other_watch_value == Some(false) {
                    self.num_conflict += 1;
                    self.dpc_ema.update(self.num_decision);
                    self.ppc_ema.update(self.num_propagation);

                    #[cfg(feature = "hashed_watch_cache")]
                    while cdb.reregister_watch_cache(propagating, watches.next().deref_watch()) {}
                    #[cfg(not(feature = "hashed_watch_cache"))]
                    cdb.restore_detached_watch_cache(propagating, source);

                    #[cfg(feature = "boundary_check")]
                    {
                        cdb[cid].moved_at = Propagate::EmitConflict(self.num_conflict, cached);
                    }

                    return Some(cid);
                }
                let lv = cdb[cid]
                    .iter()
                    .skip(1)
                    .map(|l| self.level[l.vi()])
                    .max()
                    .unwrap_or(self.root_level);
                debug_assert_eq!(cdb[cid].lit0(), cached);
                debug_assert_eq!(self.assigned(cached), None);
                assert!(other_watch_value.is_none());
                self.assign_by_implication(cached, lv, cid, None);

                #[cfg(feature = "boundary_check")]
                {
                    cdb[cid].moved_at = Propagate::BecameUnit(self.num_conflict, cached);
                }
            }
        }
        let na = self.q_head + self.num_eliminated_vars + self.num_asserted_vars;
        if self.num_best_assign <= na && 0 < self.decision_level() {
            self.best_assign = true;
            self.num_best_assign = na;
        }
        None
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
    fn propagate_sandbox<C>(&mut self, cdb: &mut C) -> Option<ClauseId>
    where
        C: ClauseDBIF,
    {
        while let Some(p) = self.trail.get(self.q_head) {
            self.q_head += 1;
            #[cfg(feature = "debug_propagation")]
            assert!(!self.var[p.vi()].is(Flag::PROPAGATED));
            #[cfg(feature = "debug_propagation")]
            self.var[p.vi()].turn_on(Flag::PROPAGATED);
            let propagating = Lit::from(usize::from(*p));
            let false_lit = !*p;

            #[cfg(feature = "boundary_check")]
            {
                self.var[p.vi()].propagated_at = self.num_conflict;
                self.var[p.vi()].state = VarState::Propagated(self.num_conflict);
            }
            // we have to drop `p` here to use self as a mutable reference again later.

            //
            //## binary loop
            //
            for (&blocker, &cid) in cdb.bi_clause_map(false_lit).iter() {
                debug_assert!(!cdb[cid].is_dead());
                debug_assert!(!self.var[blocker.vi()].is(Flag::ELIMINATED));
                debug_assert_ne!(blocker, false_lit);

                #[cfg(feature = "boundary_check")]
                debug_assert_eq!(cdb[cid].len(), 2);

                match lit_assign!(self, blocker) {
                    Some(true) => (),
                    Some(false) => return Some(cid),
                    None => {
                        debug_assert!(cdb[cid].lit0() == false_lit || cdb[cid].lit1() == false_lit);
                        self.assign_by_implication(
                            blocker,
                            self.level[false_lit.vi()],
                            cid,
                            Some(propagating),
                        );
                    }
                }
            }
            //
            //## normal clause loop
            //
            let mut source = cdb.watch_cache_iter(propagating);
            #[cfg(feature = "hashed_watch_cache")]
            let mut watches = source.iter();
            'next_clause: while let Some((cid, mut cached)) = {
                #[cfg(feature = "hashed_watch_cache")]
                {
                    watches.next().deref_watch()
                }
                #[cfg(not(feature = "hashed_watch_cache"))]
                {
                    source
                        .next()
                        .map(|index| cdb.fetch_watch_cache_entry(propagating, index))
                }
            } {
                if cdb[cid].is_dead() {
                    cdb.transform_by_restoring_watch_cache(propagating, &mut source, None);
                    continue;
                }
                debug_assert!(!self.var[cached.vi()].is(Flag::ELIMINATED));
                let mut other_watch_value = lit_assign!(self, cached);
                let mut updated_cache: Option<Lit> = None;
                if let Some(true) = other_watch_value {
                    cdb.transform_by_restoring_watch_cache(propagating, &mut source, None);

                    #[cfg(feature = "boundary_check")]
                    {
                        cdb[cid].moved_at = Propagate::SandboxCacheSatisfied(self.num_conflict);
                    }

                    continue 'next_clause;
                }
                {
                    let c = &cdb[cid];
                    let lit0 = c.lit0();
                    let lit1 = c.lit1();
                    let (false_watch_pos, other) = if false_lit == lit1 {
                        (1, lit0)
                    } else {
                        (0, lit1)
                    };

                    if cached != other {
                        cached = other;
                        other_watch_value = lit_assign!(self, other);
                        if Some(true) == other_watch_value {
                            debug_assert!(!self.var[cached.vi()].is(Flag::ELIMINATED));
                            cdb.transform_by_restoring_watch_cache(
                                propagating,
                                &mut source,
                                Some(other),
                            );

                            #[cfg(feature = "boundary_check")]
                            {
                                cdb[cid].moved_at =
                                    Propagate::SandboxCacheSatisfied(self.num_conflict);
                            }

                            continue 'next_clause;
                        }
                        updated_cache = Some(other);
                    }
                    let c = &cdb[cid];
                    debug_assert!(lit0 == false_lit || lit1 == false_lit);
                    let start = c.search_from;
                    for (k, lk) in c
                        .iter()
                        .enumerate()
                        .skip(start)
                        .chain(c.iter().enumerate().skip(2).take(start - 2))
                    {
                        if lit_assign!(self, *lk) != Some(false) {
                            let new_watch = !*lk;
                            cdb.detach_watch_cache(propagating, &mut source);
                            cdb.transform_by_updating_watch(cid, false_watch_pos, k, true);
                            cdb[cid].search_from = k + 1;
                            debug_assert!(
                                self.assigned(!new_watch) == Some(true)
                                    || self.assigned(!new_watch) == None
                            );

                            #[cfg(feature = "boundary_check")]
                            {
                                cdb[cid].moved_at = Propagate::SandboxFindNewWatch(
                                    self.num_conflict,
                                    false_lit,
                                    new_watch,
                                );
                            }

                            continue 'next_clause;
                        }
                    }
                    if false_watch_pos == 0 {
                        cdb.swap_watch(cid);
                    }
                }
                cdb.transform_by_restoring_watch_cache(propagating, &mut source, updated_cache);
                if other_watch_value == Some(false) {
                    #[cfg(feature = "hashed_watch_cache")]
                    while cdb.reregister_watch_cache(propagating, watches.next().deref_watch()) {}
                    #[cfg(not(feature = "hashed_watch_cache"))]
                    cdb.restore_detached_watch_cache(propagating, source);

                    #[cfg(feature = "boundary_check")]
                    {
                        cdb[cid].moved_at =
                            Propagate::SandboxEmitConflict(self.num_conflict, propagating);
                    }

                    return Some(cid);
                }
                let lv = cdb[cid]
                    .iter()
                    .skip(1)
                    .map(|l| self.level[l.vi()])
                    .max()
                    .unwrap_or(self.root_level);
                debug_assert_eq!(cdb[cid].lit0(), cached);
                debug_assert_eq!(self.assigned(cached), None);
                assert!(other_watch_value.is_none());
                self.assign_by_implication(cached, lv, cid, None);

                #[cfg(feature = "boundary_check")]
                {
                    cdb[cid].moved_at = Propagate::SandboxBecameUnit(self.num_conflict);
                }
            }
        }
        None
    }
    fn clear_asserted_literals<C>(&mut self, cdb: &mut C) -> MaybeInconsistent
    where
        C: ClauseDBIF,
    {
        assert_eq!(self.decision_level(), self.root_level);
        loop {
            if self.remains() {
                self.propagate(cdb)
                    .map_or(Ok(()), |cc| Err(SolverError::RootLevelConflict(Some(cc))))?;
            }
            self.propagate_at_root_level(cdb)
                .map_or(Ok(()), |cc| Err(SolverError::RootLevelConflict(Some(cc))))?;
            if self.remains() {
                self.propagate(cdb)
                    .map_or(Ok(()), |cc| Err(SolverError::RootLevelConflict(Some(cc))))?;
            } else {
                break;
            }
        }
        // wipe asserted literals from trail and increment the number of asserted vars.
        self.num_asserted_vars += self.trail.len();
        self.trail.clear();
        self.q_head = 0;
        Ok(())
    }
}

impl AssignStack {
    pub fn check(&self, (b0, b1): (Lit, Lit)) {
        assert_ne!(self.assigned(b0), Some(false));
        assert_ne!(self.assigned(b1), Some(false));
    }
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
                debug_assert!(cdb[cid]
                    .iter()
                    .all(|l| !self.var[l.vi()].is(Flag::ELIMINATED)));
                match cdb.transform_by_simplification(self, cid) {
                    RefClause::Clause(_) => (),
                    RefClause::Dead => (), // was a satisfied clause
                    RefClause::EmptyClause => return Some(cid),
                    RefClause::RegisteredClause(_) => (),
                    RefClause::UnitClause(lit) => {
                        assert!(self.assigned(lit).is_none());
                        cdb.certificate_add_assertion(lit);
                        if self.assign_at_root_level(lit).is_err() {
                            return Some(cid);
                        } else {
                            assert!(!self.locked(&cdb[cid], cid));
                            cdb.remove_clause(cid);
                        }
                    }
                }
            }
        }
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

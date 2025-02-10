// implement boolean constraint propagation, backjump
// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::AssignStack,
    crate::{
        cdb::{ClauseDB, ClauseDBIF},
        types::*,
        vam::VarActivityManager,
        var_vector::*,
    },
};

#[cfg(feature = "rephase")]
use super::rephase::AssignRephaseIF;

#[cfg(feature = "trail_saving")]
use super::TrailSavingIF;

/// API for Boolean Constraint Propagation like
/// [`propagate`](`crate::assign::PropagateIF::propagate`),
/// [`assign_by_decision`](`crate::assign::PropagateIF::assign_by_decision`),
/// [`cancel_until`](`crate::assign::PropagateIF::cancel_until`), and so on.
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
    fn assign_by_implication(
        &mut self,
        l: Lit,
        reason: AssignReason,
        #[cfg(feature = "chrono_BT")] lv: DecisionLevel,
    );
    /// unsafe assume (assign by decision); doesn't emit an exception.
    /// ## Caveat
    /// Callers have to assure the consistency after this assignment.
    fn assign_by_decision(&mut self, l: Lit);
    /// execute *backjump*.
    fn cancel_until(&mut self, lv: DecisionLevel);
    /// execute backjump in vivification sandbox
    fn backtrack_sandbox(&mut self);
    /// execute *boolean constraint propagation* or *unit propagation*.
    fn propagate(&mut self, cdb: &mut ClauseDB) -> PropagationResult;
    /// `propagate` for vivification, which allows dead clauses.
    fn propagate_sandbox(&mut self, cdb: &mut ClauseDB) -> PropagationResult;
    /// propagate then clear asserted literals
    fn clear_asserted_literals(&mut self, cdb: &mut ClauseDB) -> MaybeInconsistent;
}

impl PropagateIF for AssignStack {
    fn assign_at_root_level(&mut self, l: Lit) -> MaybeInconsistent {
        self.cancel_until(self.root_level);
        let vi = l.vi();
        debug_assert!(!VarRef(vi).is(FlagVar::ELIMINATED));
        debug_assert!(self.trail_lim.is_empty());
        VarRef(vi).set_level(self.root_level);
        match VarRef(vi).assign() {
            None => {
                VarRef::set_lit(l);
                debug_assert!(!self.trail.contains(&!l));
                self.trail.push(l);
                VarRef::make_var_asserted(vi);
                #[cfg(feature = "best_phases_tracking")]
                self.check_best_phase(vi);
                Ok(())
            }
            Some(x) if x == bool::from(l) => {
                #[cfg(feature = "boundary_check")]
                panic!("double assignment(assertion)");
                #[cfg(not(feature = "boundary_check"))]
                // Vivification tries to assign a var by propagation then can assert it.
                // To make sure the var is asserted, we need to nullify its reason.
                // || self.reason[vi] = AssignReason::None;
                // self.make_var_asserted(vi);
                Ok(())
            }
            _ => Err(SolverError::RootLevelConflict((
                l,
                VarRef(l.vi()).reason(), /* self.var[l.vi()].reason */
            ))),
        }
    }
    fn assign_by_implication(
        &mut self,
        l: Lit,
        reason: AssignReason,
        #[cfg(feature = "chrono_BT")] lv: DecisionLevel,
    ) {
        debug_assert!(usize::from(l) != 0, "Null literal is about to be enqueued");
        // The following doesn't hold anymore by using chronoBT.
        // assert!(self.trail_lim.is_empty() || !cid.is_none());
        let vi = l.vi();
        debug_assert!(!VarRef(vi).is(FlagVar::ELIMINATED));
        debug_assert_eq!(VarRef(vi).assign(), None);
        debug_assert_eq!(VarRef(vi).reason(), AssignReason::None);
        debug_assert!(self.trail.iter().all(|rl| *rl != l));
        VarRef::set_lit(l);

        #[cfg(not(feature = "chrono_BT"))]
        let lv = self.decision_level();

        VarRef(vi).set_level(lv);
        VarRef(vi).set_reason(reason);
        VarActivityManager::reward_at_assign(vi);
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
        if self.root_level == lv {
            VarRef::make_var_asserted(vi);
            #[cfg(feature = "best_phases_tracking")]
            self.check_best_phase(vi);
        }

        #[cfg(feature = "boundary_check")]
        {
            self.var[vi].propagated_at = self.num_conflict;
            self.var[vi].state = VarState::Assigned(self.num_conflict);
        }
    }
    fn assign_by_decision(&mut self, l: Lit) {
        debug_assert_ne!(VarRef(l.vi()).assign(), Some(!bool::from(l)));
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(
            !self.trail.contains(&!l),
            "asg.trail contains a strange literal",
        );
        self.level_up();
        let dl = self.trail_lim.len() as DecisionLevel;
        let vi = l.vi();
        VarRef(vi).set_level(dl);
        debug_assert!(!VarRef(vi).is(FlagVar::ELIMINATED));
        debug_assert_eq!(VarRef(vi).assign(), None);
        debug_assert_eq!(VarRef(vi).reason(), AssignReason::None);
        VarRef::set_lit(l);
        VarRef(vi).set_reason(AssignReason::Decision(self.decision_level()));
        VarActivityManager::reward_at_assign(vi);
        self.trail.push(l);
        self.num_decisions += 1;
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

        #[cfg(feature = "chrono_BT")]
        let mut unpropagated: Vec<Lit> = Vec::new();

        // We assume that backtrack is never happened in level zero.
        let lim = self.trail_lim[lv as usize];

        #[cfg(feature = "trail_saving")]
        self.save_trail(lv);

        for i in lim..self.trail.len() {
            let l = self.trail[i];
            debug_assert!(
                VarRef(l.vi()).assign().is_some(),
                "cancel_until found unassigned var in trail {}",
                l.vi(),
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

            #[cfg(feature = "chrono_BT")]
            if self.level[vi] <= lv {
                unpropagated.push(l);
                continue;
            }

            #[cfg(feature = "debug_propagation")]
            VarRef(vi).turn_off(FlagVar::PROPAGATED);
            VarRef(vi).set_flag(FlagVar::PHASE, VarRef(vi).assign().unwrap());

            #[cfg(feature = "boundary_check")]
            {
                v.propagated_at = self.num_conflict;
                v.state = VarState::Unassigned(self.num_conflict);
            }

            VarRef(vi).set_assign(None);
            VarRef(vi).set_reason(AssignReason::None);

            #[cfg(not(feature = "trail_saving"))]
            {
                VarActivityManager::reward_at_unassign(vi);
                VarActivityManager::insert_heap(vi);
            }
        }
        self.trail.truncate(lim);
        // moved below -- self.q_head = self.trail.len();
        // see https://github.com/shnarazk/splr/issues/117
        self.q_head = self.trail.len().min(self.q_head);

        #[cfg(feature = "chrono_BT")]
        self.trail.append(&mut unpropagated);

        debug_assert!(self.trail.iter().all(|l| VarRef(l.vi()).assign().is_some()));
        debug_assert!(self.trail.iter().all(|k| !self.trail.contains(&!*k)));
        self.trail_lim.truncate(lv as usize);
        // assert!(lim < self.q_head) doesn't hold sometimes in chronoBT.
        if lv == self.root_level {
            self.num_restarts += 1;
            self.cpr_ema.update(self.num_conflicts);
        } else {
            #[cfg(feature = "assign_rate")]
            self.assign_rate.update(
                self.num_vars
                    - self.num_asserted_vars
                    - self.num_eliminated_vars
                    - self.trail.len(),
            );
        }

        debug_assert!(
            self.q_head == 0 || VarRef(self.trail[self.q_head - 1].vi()).assign().is_some()
        );
        #[cfg(feature = "debug_propagation")]
        debug_assert!(
            self.q_head == 0 || self.var[self.trail[self.q_head - 1].vi()].is(FlagVar::PROPAGATED)
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
            debug_assert!(self.root_level < VarRef(vi).level());
            VarRef(vi).set_assign(None);
            VarRef(vi).set_reason(AssignReason::None);
            // self.insert_heap(vi);
            VarActivityManager::insert_heap(vi);
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
    fn propagate(&mut self, cdb: &mut ClauseDB) -> PropagationResult {
        #[cfg(feature = "boundary_check")]
        macro_rules! check_in {
            ($cid: expr, $tag :expr) => {
                cdb[$cid].moved_at = $tag;
            };
        }
        #[cfg(not(feature = "boundary_check"))]
        macro_rules! check_in {
            ($cid: expr, $tag :expr) => {};
        }

        macro_rules! conflict_path {
            ($lit: expr, $reason: expr) => {
                self.dpc_ema.update(self.num_decisions);
                self.ppc_ema.update(self.num_propagations);
                self.num_conflicts += 1;
                return Err(($lit, $reason));
            };
        }

        #[cfg(feature = "suppress_reason_chain")]
        macro_rules! minimized_reason {
            ($lit: expr) => {
                if let r @ AssignReason::BinaryLink(_) = self.reason[$lit.vi()] {
                    r
                } else {
                    AssignReason::BinaryLink($lit)
                }
            };
        }
        #[cfg(not(feature = "suppress_reason_chain"))]
        macro_rules! minimized_reason {
            ($lit: expr) => {
                AssignReason::BinaryLink($lit)
            };
        }

        #[cfg(feature = "trail_saving")]
        macro_rules! from_saved_trail {
            () => {
                if let cc @ Err(_) = self.reuse_saved_trail(cdb) {
                    self.num_propagations += 1;
                    self.num_conflicts += 1;
                    self.num_reconflict += 1;
                    self.dpc_ema.update(self.num_decisions);
                    self.ppc_ema.update(self.num_propagations);
                    return cc;
                }
            };
        }
        #[cfg(not(feature = "trail_saving"))]
        macro_rules! from_saved_trail {
            () => {};
        }

        let dl = self.decision_level();
        from_saved_trail!();
        while let Some(p) = self.trail.get(self.q_head) {
            self.num_propagations += 1;
            self.q_head += 1;
            #[cfg(feature = "debug_propagation")]
            {
                assert!(!self.var[p.vi()].is(FlagVar::PROPAGATED));
                self.var[p.vi()].turn_on(FlagVar::PROPAGATED);
            }
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
            for (blocker, cid) in cdb.binary_links(false_lit).iter().copied() {
                debug_assert!(!cdb[cid].is_dead());
                debug_assert!(!VarRef(blocker.vi()).is(FlagVar::ELIMINATED));
                debug_assert_ne!(blocker, false_lit);
                debug_assert_eq!(cdb[cid].len(), 2);
                match VarRef::lit_assigned(blocker) {
                    Some(true) => (),
                    Some(false) => {
                        check_in!(
                            cid,
                            Propagate::EmitConflict(self.num_conflicts + 1, blocker)
                        );
                        conflict_path!(blocker, minimized_reason!(propagating));
                    }
                    None => {
                        debug_assert!(cdb[cid].lit0() == false_lit || cdb[cid].lit1() == false_lit);
                        self.assign_by_implication(
                            blocker,
                            minimized_reason!(propagating),
                            #[cfg(feature = "chrono_BT")]
                            self.level[propagating.vi()],
                        );
                    }
                }
            }
            //
            //## normal clause loop
            //
            let mut source = cdb.watch_cache_iter(propagating);
            'next_clause: while let Some((cid, mut cached)) = source
                .next()
                .map(|index| cdb.fetch_watch_cache_entry(propagating, index))
            {
                #[cfg(feature = "boundary_check")]
                debug_assert!(
                    !cdb[cid].is_dead(),
                    "dead clause in propagation: {:?}",
                    cdb.is_garbage_collected(cid),
                );
                debug_assert!(!VarRef(cached.vi()).is(FlagVar::ELIMINATED));
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
                let mut other_watch_value = VarRef::lit_assigned(cached);
                let mut updated_cache: Option<Lit> = None;
                if Some(true) == other_watch_value {
                    #[cfg(feature = "maintain_watch_cache")]
                    debug_assert!(cdb[cid].lit0() == cached || cdb[cid].lit1() == cached);

                    // In this path, we use only `AssignStack::assign`.
                    // assert!(w.blocker == cdb[w.c].lits[0] || w.blocker == cdb[w.c].lits[1]);
                    cdb.transform_by_restoring_watch_cache(propagating, &mut source, None);
                    check_in!(cid, Propagate::CacheSatisfied(self.num_conflict));
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
                        other_watch_value = VarRef::lit_assigned(other);
                        if Some(true) == other_watch_value {
                            debug_assert!(!VarRef(other.vi()).is(FlagVar::ELIMINATED));
                            // In this path, we use only `AssignStack::assign`.
                            cdb.transform_by_restoring_watch_cache(
                                propagating,
                                &mut source,
                                Some(other),
                            );
                            check_in!(cid, Propagate::CacheSatisfied(self.num_conflict));
                            continue 'next_clause;
                        }
                        updated_cache = Some(other);
                    }
                    let c = &cdb[cid];
                    debug_assert!(lit0 == false_lit || lit1 == false_lit);
                    //
                    //## Search an un-falsified literal
                    //
                    // Gathering good literals at the beginning of lits.
                    let start = c.search_from;
                    for (k, lk) in c
                        .iter()
                        .enumerate()
                        .skip(start as usize)
                        .chain(c.iter().enumerate().skip(2).take(start as usize - 2))
                    {
                        if VarRef::lit_assigned(*lk) != Some(false) {
                            let new_watch = !*lk;
                            cdb.detach_watch_cache(propagating, &mut source);
                            cdb.transform_by_updating_watch(cid, false_watch_pos, k, true);
                            cdb[cid].search_from = (k + 1) as u16;
                            debug_assert_ne!(VarRef::lit_assigned(new_watch), Some(true));
                            check_in!(
                                cid,
                                Propagate::FindNewWatch(self.num_conflict, propagating, new_watch)
                            );
                            continue 'next_clause;
                        }
                    }
                    if false_watch_pos == 0 {
                        cdb.swap_watch(cid);
                    }
                }
                cdb.transform_by_restoring_watch_cache(propagating, &mut source, updated_cache);
                if other_watch_value == Some(false) {
                    check_in!(cid, Propagate::EmitConflict(self.num_conflict + 1, cached));
                    conflict_path!(cached, AssignReason::Implication(cid));
                }

                #[cfg(feature = "chrono_BT")]
                let dl = cdb[cid]
                    .iter()
                    .skip(1)
                    .map(|l| self.level[l.vi()])
                    .max()
                    .unwrap_or(self.root_level);

                debug_assert_eq!(cdb[cid].lit0(), cached);
                debug_assert_eq!(VarRef::lit_assigned(cached), None);
                debug_assert!(other_watch_value.is_none());
                self.assign_by_implication(
                    cached,
                    AssignReason::Implication(cid),
                    #[cfg(feature = "chrono_BT")]
                    dl,
                );
                check_in!(cid, Propagate::BecameUnit(self.num_conflict, cached));
            }
            from_saved_trail!();
        }
        let na = self.q_head + self.num_eliminated_vars + self.num_asserted_vars;
        if self.num_best_assign <= na && 0 < dl {
            self.best_assign = true;
            self.num_best_assign = na;
        }
        Ok(())
    }
    //
    //## How to generate propagate_sandbox from propagate
    //
    // 1. copy it
    // 1. delete codes about reward
    // 1. delete codes about best-phases
    // 1. delete codes about search_from
    // 1. delete codes about trail_saving
    // 1. delete codes about stat counters: num_*, ema_*
    // 1. delete comments
    // 1. (allow dead clauses)
    // 1. (allow eliminated vars)
    //
    fn propagate_sandbox(&mut self, cdb: &mut ClauseDB) -> PropagationResult {
        #[cfg(feature = "boundary_check")]
        macro_rules! check_in {
            ($cid: expr, $tag :expr) => {
                cdb[$cid].moved_at = $tag;
            };
        }
        #[cfg(not(feature = "boundary_check"))]
        macro_rules! check_in {
            ($cid: expr, $tag :expr) => {};
        }
        macro_rules! conflict_path {
            ($lit: expr, $reason: expr) => {
                return Err(($lit, $reason))
            };
        }
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
            //
            //## binary loop
            //
            for (blocker, cid) in cdb.binary_links(false_lit).iter().copied() {
                debug_assert!(!cdb[cid].is_dead());
                debug_assert!(!VarRef(blocker.vi()).is(FlagVar::ELIMINATED));
                debug_assert_ne!(blocker, false_lit);

                #[cfg(feature = "boundary_check")]
                debug_assert_eq!(cdb[*cid].len(), 2);

                match VarRef::lit_assigned(blocker) {
                    Some(true) => (),
                    Some(false) => conflict_path!(blocker, AssignReason::BinaryLink(propagating)),
                    None => {
                        debug_assert!(cdb[cid].lit0() == false_lit || cdb[cid].lit1() == false_lit);

                        self.assign_by_implication(
                            blocker,
                            AssignReason::BinaryLink(propagating),
                            #[cfg(feature = "chrono_BT")]
                            self.level[false_lit.vi()],
                        );
                    }
                }
            }
            //
            //## normal clause loop
            //
            let mut source = cdb.watch_cache_iter(propagating);
            'next_clause: while let Some((cid, mut cached)) = source
                .next()
                .map(|index| cdb.fetch_watch_cache_entry(propagating, index))
            {
                if cdb[cid].is_dead() {
                    cdb.transform_by_restoring_watch_cache(propagating, &mut source, None);
                    continue;
                }
                debug_assert!(!VarRef(cached.vi()).is(FlagVar::ELIMINATED));
                let mut other_watch_value = VarRef::lit_assigned(cached);
                let mut updated_cache: Option<Lit> = None;
                if matches!(other_watch_value, Some(true)) {
                    cdb.transform_by_restoring_watch_cache(propagating, &mut source, None);
                    check_in!(cid, Propagate::SandboxCacheSatisfied(self.num_conflict));
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
                        other_watch_value = VarRef::lit_assigned(other);
                        if Some(true) == other_watch_value {
                            debug_assert!(!VarRef(cached.vi()).is(FlagVar::ELIMINATED));
                            cdb.transform_by_restoring_watch_cache(
                                propagating,
                                &mut source,
                                Some(other),
                            );
                            check_in!(cid, Propagate::SandboxCacheSatisfied(self.num_conflict));
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
                        .skip(start as usize)
                        .chain(c.iter().enumerate().skip(2).take(start as usize - 2))
                    {
                        if VarRef::lit_assigned(*lk) != Some(false) {
                            let new_watch = !*lk;
                            cdb.detach_watch_cache(propagating, &mut source);
                            cdb.transform_by_updating_watch(cid, false_watch_pos, k, true);
                            cdb[cid].search_from = (k as u16).saturating_add(1);
                            debug_assert!(
                                VarRef::lit_assigned(!new_watch) == Some(true)
                                    || VarRef::lit_assigned(!new_watch).is_none()
                            );
                            check_in!(
                                cid,
                                Propagate::SandboxFindNewWatch(
                                    self.num_conflict,
                                    false_lit,
                                    new_watch,
                                )
                            );
                            continue 'next_clause;
                        }
                    }
                    if false_watch_pos == 0 {
                        cdb.swap_watch(cid);
                    }
                }
                cdb.transform_by_restoring_watch_cache(propagating, &mut source, updated_cache);
                if other_watch_value == Some(false) {
                    check_in!(
                        cid,
                        Propagate::SandboxEmitConflict(self.num_conflict, propagating)
                    );
                    return Err((cached, AssignReason::Implication(cid)));
                }

                #[cfg(feature = "chrono_BT")]
                let dl = cdb[cid]
                    .iter()
                    .skip(1)
                    .map(|l| self.level[l.vi()])
                    .max()
                    .unwrap_or(self.root_level);
                debug_assert_eq!(cdb[cid].lit0(), cached);
                debug_assert_eq!(VarRef::lit_assigned(cached), None);
                debug_assert!(other_watch_value.is_none());

                self.assign_by_implication(
                    cached,
                    AssignReason::Implication(cid),
                    #[cfg(feature = "chrono_BT")]
                    dl,
                );
                check_in!(cid, Propagate::SandboxBecameUnit(self.num_conflict));
            }
        }
        Ok(())
    }
    fn clear_asserted_literals(&mut self, cdb: &mut ClauseDB) -> MaybeInconsistent {
        debug_assert_eq!(self.decision_level(), self.root_level);
        loop {
            if self.remains() {
                self.propagate_sandbox(cdb)
                    .map_err(SolverError::RootLevelConflict)?;
            }
            self.propagate_at_root_level(cdb)?;
            if self.remains() {
                self.propagate_sandbox(cdb)
                    .map_err(SolverError::RootLevelConflict)?;
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
    #[allow(dead_code)]
    fn check(&self, (b0, b1): (Lit, Lit)) {
        assert_ne!(VarRef::lit_assigned(b0), Some(false));
        assert_ne!(VarRef::lit_assigned(b1), Some(false));
    }
    /// simplify clauses by propagating literals at root level.
    fn propagate_at_root_level(&mut self, cdb: &mut ClauseDB) -> MaybeInconsistent {
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
                    .all(|l| !VarRef(l.vi()).is(FlagVar::ELIMINATED)));
                match cdb.transform_by_simplification(cid) {
                    RefClause::Clause(_) => (),
                    RefClause::Dead => (), // was a satisfied clause
                    RefClause::EmptyClause => return Err(SolverError::EmptyClause),
                    RefClause::RegisteredClause(_) => (),
                    RefClause::UnitClause(lit) => {
                        debug_assert!(VarRef::lit_assigned(lit).is_none());
                        cdb.certificate_add_assertion(lit);
                        self.assign_at_root_level(lit)?;
                        cdb.remove_clause(cid);
                    }
                }
            }
        }
        Ok(())
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
                if let Some(b) = VarRef(vi).assign() {
                    self.best_phases.insert(vi, (b, VarRef(vi).reason()));
                }
            }
        }
        self.build_best_at = self.num_propagations;
        #[cfg(feature = "rephase")]
        {
            self.phase_age = 0;
        }
    }
}

/// implement boolean constraint propagation, backjump
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{AssignIF, AssignStack, VarHeapIF, VarManipulateIF},
    crate::{
        cdb::{ClauseDBIF, WatcherLinkIF},
        types::*,
    },
};

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
    fn propagate(&mut self, cdb: &mut impl ClauseDBIF) -> PropagationResult;
    /// `propagate` for vivification, which allows dead clauses.
    fn propagate_sandbox(&mut self, cdb: &mut impl ClauseDBIF) -> PropagationResult;
    /// propagate then clear asserted literals
    fn clear_asserted_literals(&mut self, cdb: &mut impl ClauseDBIF) -> MaybeInconsistent;
}

macro_rules! lit_assign {
    ($var: expr, $lit: expr) => {
        match $var.assign {
            Some(x) if !bool::from($lit) => Some(!x),
            x => x,
        }
    };
}

impl PropagateIF for AssignStack {
    fn assign_at_root_level(&mut self, l: Lit) -> MaybeInconsistent {
        self.cancel_until(self.root_level);
        let vi = l.vi();
        debug_assert!(vi < self.var.len());
        let var = &mut self.var[vi];
        debug_assert!(!var.is(FlagVar::ELIMINATED));
        debug_assert!(self.trail_lim.is_empty());
        var.level = self.root_level;
        match var.assign {
            None => {
                var.assign = Some(bool::from(l));
                debug_assert!(!self.trail.contains(&!l));
                self.trail.push(l);
                self.make_var_asserted(vi);
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
            _ => Err(SolverError::RootLevelConflict((l, var.reason))),
        }
    }
    fn assign_by_implication(
        &mut self,
        l: Lit,
        reason: AssignReason,
        #[cfg(feature = "chrono_BT")] lv: DecisionLevel,
    ) {
        debug_assert!(usize::from(l) != 0, "Null literal is about to be enqueued");
        debug_assert!(l.vi() < self.var.len());
        // The following doesn't hold anymore by using chronoBT.
        // assert!(self.trail_lim.is_empty() || !cid.is_none());
        let vi = l.vi();
        // debug_assert!([Some(bool::from(l)), None].contains(&self.var[vi].assign));
        // debug_assert!(self.trail.iter().all(|rl| *rl != l));

        #[cfg(not(feature = "chrono_BT"))]
        let lv = self.decision_level();

        debug_assert!(!self.var[vi].is(FlagVar::ELIMINATED));
        let var = &mut self.var[vi];
        debug_assert_eq!(var.assign, None);
        debug_assert_eq!(var.reason, AssignReason::None);
        var.assign = Some(bool::from(l));
        var.level = lv;
        var.reason = reason;
        self.reward_at_assign(vi);
        // debug_assert!(!self.trail.contains(&l));
        // debug_assert!(!self.trail.contains(&!l));
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
        // debug_assert!([Some(bool::from(l)), None].contains(&self.var[l.vi()].assign));
        debug_assert!(l.vi() < self.var.len());
        // debug_assert!(!self.trail.contains(&l));
        // debug_assert!(
        //     !self.trail.contains(&!l),
        //     "asg.trail contains a strange literal",
        // );
        self.level_up();
        let dl = self.trail_lim.len() as DecisionLevel;
        let reason = AssignReason::Decision(self.decision_level());
        let vi = l.vi();
        let var = &mut self.var[vi];
        var.level = dl;
        debug_assert!(!var.is(FlagVar::ELIMINATED));
        debug_assert_eq!(var.assign, None);
        debug_assert_eq!(var.reason, AssignReason::None);
        var.assign = Some(bool::from(l));
        var.reason = reason;
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

        #[cfg(feature = "chrono_BT")]
        let mut unpropagated: Vec<Lit> = Vec::new();

        // We assume that backtrack is never happened in level zero.
        let lim = self.trail_lim[lv as usize];

        #[cfg(feature = "trail_saving")]
        self.save_trail(lv);

        for i in lim..self.trail.len() {
            let l = self.trail[i];
            let vi = l.vi();
            let var = &mut self.var[vi];
            debug_assert!(
                var.assign.is_some(),
                "cancel_until found unassigned var in trail {}{:?}",
                l.vi(),
                &self.var[l.vi()],
            );
            #[cfg(feature = "debug_propagation")]
            debug_assert!(self.q_head <= i || self.var[vi].is(Flag::PROPAGATED),
                    "unpropagated assigned level-{} var {:?},{:?} (loc:{} in trail{:?}) found, staying at level {}",
                    var.level,
                    var.var,
                    var.reason,
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
            var.turn_off(FlagVar::PROPAGATED);
            var.set(FlagVar::PHASE, var.assign.unwrap());

            #[cfg(feature = "boundary_check")]
            {
                var.propagated_at = self.num_conflict;
                var.state = VarState::Unassigned(self.num_conflict);
            }

            var.assign = None;
            var.reason = AssignReason::None;

            #[cfg(not(feature = "trail_saving"))]
            {
                self.reward_at_unassign(vi);
                self.insert_heap(vi);
            }
        }
        self.trail.truncate(lim);
        // moved below -- self.q_head = self.trail.len();
        // see https://github.com/shnarazk/splr/issues/117
        self.q_head = self.trail.len().min(self.q_head);

        #[cfg(feature = "chrono_BT")]
        self.trail.append(&mut unpropagated);

        // debug_assert!(self.trail.iter().all(|l| self.var[l.vi()].assign.is_some()));
        // debug_assert!(self.trail.iter().all(|k| !self.trail.contains(&!*k)));
        self.trail_lim.truncate(lv as usize);
        // assert!(lim < self.q_head) doesn't hold sometimes in chronoBT.
        if lv == self.root_level {
            self.num_restart += 1;
            self.cpr_ema.update(self.num_conflict);
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
            self.q_head == 0 || self.var[self.trail[self.q_head - 1].vi()].assign.is_some()
        );
        #[cfg(feature = "debug_propagation")]
        debug_assert!(
            self.q_head == 0 || self.var[self.trail[self.q_head - 1].vi()].is(FlagVar::PROPAGATED)
        );
        self.rebuild_base_level = self.decision_level();
    }
    fn backtrack_sandbox(&mut self) {
        if self.trail_lim.is_empty() {
            return;
        }
        let lim = self.trail_lim[self.root_level as usize];
        for i in lim..self.trail.len() {
            let l = self.trail[i];
            let vi = l.vi();
            let var = &mut self.var[vi];
            debug_assert!(self.root_level < var.level);
            var.assign = None;
            var.reason = AssignReason::None;
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
    fn propagate(&mut self, cdb: &mut impl ClauseDBIF) -> PropagationResult {
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
                self.dpc_ema.update(self.num_decision);
                self.ppc_ema.update(self.num_propagation);
                self.num_conflict += 1;
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
                    self.num_propagation += 1;
                    self.num_conflict += 1;
                    self.num_reconflict += 1;
                    self.dpc_ema.update(self.num_decision);
                    self.ppc_ema.update(self.num_propagation);
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
            self.num_propagation += 1;
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
                let var = &self.var[blocker.vi()];
                debug_assert!(!cdb[cid].is_dead());
                debug_assert!(!var.is(FlagVar::ELIMINATED));
                debug_assert_ne!(blocker, false_lit);
                debug_assert_eq!(cdb[cid].len(), 2);
                match lit_assign!(var, blocker) {
                    Some(true) => (),
                    Some(false) => {
                        check_in!(cid, Propagate::EmitConflict(self.num_conflict + 1, blocker));
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
            let mut wli = cdb.get_first_watch(propagating);
            'next_clause: while !wli.is_none() {
                let (ci, false_index) = wli.indices();
                let c = &mut cdb[ci];
                // c.turn_off(FlagClause::PROPAGATEBY1);
                let other: Lit = *c.iter().nth(1 - false_index).unwrap();
                let ovi: usize = other.vi();
                let other_value = lit_assign!(self.var[ovi], other);
                if other_value == Some(true) {
                    let next = c.next_watch(false_index);
                    assert_ne!(wli, next);
                    wli = next;
                    continue 'next_clause;
                }
                if other_value == Some(false) && self.var[ovi].level < self.rebuild_base_level {
                    // debug_assert!(c
                    //     .iter()
                    //     .all(|l| lit_assign!(self.var[l.vi()], *l) == Some(false)));
                    c.set(FlagClause::PROPAGATEBY1, false_index == 0);
                    assert_eq!(other, c[1 - false_index]);
                    check_in!(ci, Propagate::EmitConflict(self.num_conflict + 1, other));
                    conflict_path!(other, AssignReason::Implication(wli.as_ci()));
                }
                let start = c.search_from as usize;
                let len = c.len() - 2;
                for i in 0..len {
                    let k: usize = (i + start) % len + 2;
                    let lk: Lit = c[k];
                    if lit_assign!(self.var[lk.vi()], lk) != Some(false) {
                        let next: WatchLiteralIndex = cdb.transform_by_updating_watch(wli, k);
                        debug_assert_ne!(self.assigned(!lk), Some(true));
                        check_in!(
                            ci,
                            Propagate::FindNewWatch(self.num_conflict, propagating, !lk)
                        );
                        assert!(2 < cdb[ci].len());
                        assert_ne!(wli, next);
                        wli = next;
                        continue 'next_clause;
                    }
                }
                c.set(FlagClause::PROPAGATEBY1, false_index == 0);
                if other_value == Some(false) {
                    check_in!(ci, Propagate::EmitConflict(self.num_conflict + 1, other));
                    conflict_path!(other, AssignReason::Implication(wli.as_ci()));
                } else {
                    #[cfg(feature = "chrono_BT")]
                    let dl = cdb[cid]
                        .iter()
                        .skip(1)
                        .map(|l| self.level[l.vi()])
                        .max()
                        .unwrap_or(self.root_level);

                    debug_assert_eq!(self.assigned(other), None);
                    if ci == 261 {
                        println!(
                            "unit propagation: {other} by {ci} at {dl}: {} {c:?}",
                            false_index == 0
                        );
                    }
                    self.assign_by_implication(
                        other,
                        AssignReason::Implication(wli.as_ci()),
                        #[cfg(feature = "chrono_BT")]
                        dl,
                    );
                    check_in!(cid, Propagate::BecameUnit(self.num_conflict, cached));
                    wli = c.next_watch(false_index);
                }
            }
            from_saved_trail!();
        }
        let na: usize = self.q_head + self.num_eliminated_vars + self.num_asserted_vars;
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
    fn propagate_sandbox(&mut self, cdb: &mut impl ClauseDBIF) -> PropagationResult {
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
            #[cfg(feature = "debug_propagation")]
            assert!(!self.var[p.vi()].is(Flag::PROPAGATED));
            #[cfg(feature = "debug_propagation")]
            self.var[p.vi()].turn_on(Flag::PROPAGATED);

            self.q_head += 1;
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
            for (blocker, ci) in cdb.binary_links(false_lit).iter().copied() {
                // In some configurations, dead clauses can exist here.
                if cdb[ci].is_dead() {
                    continue;
                }
                debug_assert!(!self.var[blocker.vi()].is(FlagVar::ELIMINATED));
                debug_assert_ne!(blocker, false_lit);

                #[cfg(feature = "boundary_check")]
                debug_assert_eq!(cdb[*cid].len(), 2);

                match lit_assign!(self.var[blocker.vi()], blocker) {
                    Some(true) => (),
                    Some(false) => conflict_path!(blocker, AssignReason::BinaryLink(propagating)),
                    None => {
                        debug_assert!(cdb[ci].lit0() == false_lit || cdb[ci].lit1() == false_lit);

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
            let mut wli = cdb.get_first_watch(propagating);
            'next_clause: while !wli.is_none() {
                let (ci, false_index) = wli.indices();
                let c = &mut cdb[ci];
                // if c.is_dead() {
                //     ci = c.next_for_lit(propagating);
                //     continue 'next_clause;
                // }
                let other = *c.iter().nth(1 - false_index).unwrap();
                let ovi = other.vi();
                let other_value = lit_assign!(self.var[ovi], other);
                if other_value == Some(true) {
                    wli = c.next_watch(false_index);
                    continue 'next_clause;
                }
                let start = c.search_from as usize;
                let len = c.len() - 2;
                for i in 0..c.len() - 2 {
                    let k = (i + start) % len + 2;
                    let lk = c[k];
                    if lit_assign!(self.var[lk.vi()], lk) != Some(false) {
                        let next = cdb.transform_by_updating_watch(wli, k);
                        check_in!(
                            ci,
                            Propagate::SandboxFindNewWatch(self.num_conflict, false_lit, !lk)
                        );
                        wli = next;
                        continue 'next_clause;
                    }
                }
                c.set(FlagClause::PROPAGATEBY1, false_index == 0);
                if other_value == Some(false) {
                    check_in!(
                        ci,
                        Propagate::SandboxEmitConflict(self.num_conflict, propagating)
                    );
                    return Err((other, AssignReason::Implication(wli.as_ci())));
                }
                self.assign_by_implication(other, AssignReason::Implication(wli.as_ci()));
                check_in!(cid, Propagate::SandboxBecameUnit(self.num_conflict));
                wli = c.next_watch(false_index);
            }
        }
        Ok(())
    }
    fn clear_asserted_literals(&mut self, cdb: &mut impl ClauseDBIF) -> MaybeInconsistent {
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
        assert_ne!(self.assigned(b0), Some(false));
        assert_ne!(self.assigned(b1), Some(false));
    }
    /// clear unpropagated literal and satisfied clauses at root_level
    fn propagate_at_root_level(&mut self, cdb: &mut impl ClauseDBIF) -> MaybeInconsistent {
        debug_assert_eq!(self.decision_level(), self.root_level);
        let mut num_propagated = 0;
        while num_propagated < self.trail.len() {
            num_propagated = self.trail.len();
            for ci in 1..cdb.len() {
                if cdb[ci].is_dead() {
                    continue;
                }
                // debug_assert!(cdb[ci]
                //     .iter()
                //     .all(|l| !self.var[l.vi()].is(FlagVar::ELIMINATED)));
                match cdb.transform_by_simplification(self, ci) {
                    RefClause::Clause(_) => (),
                    RefClause::Dead => (), // was a satisfied clause
                    RefClause::EmptyClause => return Err(SolverError::EmptyClause),
                    RefClause::RegisteredClause(_) => (),
                    RefClause::UnitClause(lit) => {
                        debug_assert!(self.assigned(lit).is_none());
                        cdb.certificate_add_assertion(lit);
                        self.assign_at_root_level(lit)?;
                        cdb.delete_clause(ci);
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
                let var = &self.var[vi];
                if let Some(b) = var.assign {
                    self.best_phases.insert(vi, (b, var.reason));
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

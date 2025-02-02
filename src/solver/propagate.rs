// implement boolean constraint propagation, backjump
// This version can handle Chronological and Non Chronological Backtrack.
use crate::{
    assign::{AssignIF, AssignStack},
    cdb::ClauseDBIF,
    types::*,
    var_activity::{VarActivityManager, VarActivityManagerIF},
};

#[cfg(feature = "trail_saving")]
use crate::assign::TrailSavingIF;

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
    fn assign_at_root_level<'a>(&'a mut self, l: Lit<'a>) -> MaybeInconsistent;
    /// unsafe enqueue (assign by implication); doesn't emit an exception.
    ///
    /// ## Warning
    /// Callers must assure the consistency after this assignment.
    fn assign_by_implication<'a>(
        &'a mut self,
        vars: &'a mut [Var],
        l: Lit<'a>,
        reason: AssignReason<'a>,
        #[cfg(feature = "chrono_BT")] lv: DecisionLevel,
    );
    /// unsafe assume (assign by decision); doesn't emit an exception.
    /// ## Caveat
    /// Callers have to assure the consistency after this assignment.
    fn assign_by_decision<'a>(&'a mut self, l: Lit<'a>);
    /// execute *backjump*.
    fn cancel_until(&mut self, lv: DecisionLevel);
    /// execute backjump in vivification sandbox
    fn backtrack_sandbox(&mut self);
    /// execute *boolean constraint propagation* or *unit propagation*.
    fn propagate<'a>(&'a mut self, cdb: &'a mut impl ClauseDBIF<'a>) -> PropagationResult<'a>;
    /// `propagate` for vivification, which allows dead clauses.
    fn propagate_sandbox<'a>(
        &'a mut self,
        cdb: &'a mut impl ClauseDBIF<'a>,
    ) -> PropagationResult<'a>;
    /// propagate then clear asserted literals
    fn clear_asserted_literals<'a>(
        &'a mut self,
        cdb: &'a mut impl ClauseDBIF<'a>,
    ) -> MaybeInconsistent;
}

pub fn assign_at_root_level<'a>(
    // vars: &'a mut [Var<'a>],
    asg: &'a mut AssignStack<'a>,
    vam: &'a mut VarActivityManager,
    l: Lit<'a>,
    v: &'a mut Var<'a>,
) -> MaybeInconsistent {
    assert_eq!(asg.decision_level(), asg.root_level);
    debug_assert!(!v.is(FlagVar::ELIMINATED));
    debug_assert!(asg.trail_lim.is_empty());
    v.level = asg.root_level;
    match v.assign {
        None => {
            v.assign = Some(l.possitive);
            debug_assert!(!asg.trail.contains(&!l));
            asg.trail.push(l);
            asg.make_var_asserted(vam, v);
            Ok(())
        }
        Some(x) if x == l.possitive => {
            #[cfg(feature = "boundary_check")]
            panic!("double assignment(assertion)");
            #[cfg(not(feature = "boundary_check"))]
            // Vivification tries to assign a var by propagation then can assert it.
            // To make sure the var is asserted, we need to nullify its reason.
            // || self.reason[vi] = AssignReason::None;
            // self.make_var_asserted(vi);
            Ok(())
        }
        _ => Err(SolverError::RootLevelConflict),
    }
}
fn assign_by_implication<'a>(
    vars: &'a mut [Var<'a>],
    asg: &'a mut AssignStack<'a>,
    vam: &'a mut VarActivityManager,
    l: Lit<'a>,
    reason: AssignReason<'a>,
    #[cfg(feature = "chrono_BT")] lv: DecisionLevel,
) {
    debug_assert!(usize::from(l) != 0, "Null literal is about to be enqueued");
    // The following doesn't hold anymore by using chronoBT.
    // assert!(self.trail_lim.is_empty() || !cid.is_none());
    let vi = l.var.id;
    let v = &mut vars[vi];
    debug_assert!(!l.var.is(FlagVar::ELIMINATED));
    debug_assert!(v.assign == Some(bool::from(l)) || v.assign.is_none());
    debug_assert_eq!(l.var.assign, None);
    debug_assert_eq!(l.var.reason, AssignReason::None);
    debug_assert!(asg.trail.iter().all(|rl| *rl != l));
    v.assign = Some(l.possitive);

    #[cfg(not(feature = "chrono_BT"))]
    let lv = asg.decision_level();

    v.level = lv;
    v.reason = reason;
    vam.reward_at_assign(v);
    debug_assert!(!asg.trail.contains(&l));
    debug_assert!(!asg.trail.contains(&!l));
    asg.trail.push(l);
    if asg.root_level == lv {
        asg.make_var_asserted(heap, vi);
    }

    #[cfg(feature = "boundary_check")]
    {
        self.var[vi].propagated_at = self.num_conflict;
        self.var[vi].state = VarState::Assigned(self.num_conflict);
    }
}
fn assign_by_decision<'a>(
    vars: &'a mut [Var<'a>],
    asg: &'a mut AssignStack<'a>,
    vam: &mut VarActivityManager,
    l: Lit<'a>,
) {
    debug_assert!(l.var.assign == Some(bool::from(l)) || l.var.assign.is_none());
    debug_assert!(!asg.trail.contains(&l));
    debug_assert!(
        !asg.trail.contains(&!l),
        "asg.trail contains a strange literal",
    );
    asg.level_up();
    let dl = asg.trail_lim.len() as DecisionLevel;
    let vi = l.var.id;
    let v = &mut vars[vi];
    v.level = dl;
    debug_assert!(!v.is(FlagVar::ELIMINATED));
    debug_assert_eq!(v.assign, None);
    debug_assert_eq!(v.reason, AssignReason::None);
    v.assign = Some(l.possitive);
    v.reason = AssignReason::Decision(asg.decision_level());
    vam.reward_at_assign(v);
    asg.trail.push(l);
    asg.num_decision += 1;
    debug_assert!(asg.q_head < asg.trail.len());
}
pub fn cancel_until<'a, 'b>(
    vars: &'b mut [Var<'a>],
    asg: &'b mut AssignStack<'a>,
    vam: &'b mut VarActivityManager,
    lv: DecisionLevel,
) {
    if asg.trail_lim.len() as u32 <= lv {
        return;
    }
    if asg.best_assign {
        asg.save_best_phases();
        asg.best_assign = false;
    }

    #[cfg(feature = "chrono_BT")]
    let mut unpropagated: Vec<Lit<'a>> = Vec::new();

    // We assume that backtrack is never happened in level zero.
    let lim = asg.trail_lim[lv as usize];

    #[cfg(feature = "trail_saving")]
    asg.save_trail(vars, vam, lv);

    for i in lim..asg.trail.len() {
        let l = asg.trail[i];
        debug_assert!(
            l.var.assign.is_some(),
            "cancel_until found unassigned var in trail {}{:?}",
            l.var.id,
            l.var,
        );
        let vi = l.var.id;
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

        let v = &mut vars[vi];
        #[cfg(feature = "debug_propagation")]
        v.turn_off(FlagVar::PROPAGATED);
        v.set(FlagVar::PHASE, v.assign.unwrap());

        #[cfg(feature = "boundary_check")]
        {
            v.propagated_at = self.num_conflict;
            v.state = VarState::Unassigned(self.num_conflict);
        }

        v.assign = None;
        v.reason = AssignReason::None;

        #[cfg(not(feature = "trail_saving"))]
        {
            vam.reward_at_unassign(v);
            vam.insert_heap(vi);
        }
    }
    asg.trail.truncate(lim);
    // moved below -- self.q_head = self.trail.len();
    // see https://github.com/shnarazk/splr/issues/117
    asg.q_head = asg.trail.len().min(asg.q_head);

    #[cfg(feature = "chrono_BT")]
    self.trail.append(&mut unpropagated);

    debug_assert!(asg.trail.iter().all(|l| l.var.assign.is_some()));
    debug_assert!(asg.trail.iter().all(|k| !asg.trail.contains(&!*k)));
    asg.trail_lim.truncate(lv as usize);
    // assert!(lim < self.q_head) doesn't hold sometimes in chronoBT.
    if lv == asg.root_level {
        asg.num_restart += 1;
        asg.cpr_ema.update(asg.num_conflict);
    } else {
        #[cfg(feature = "assign_rate")]
        self.assign_rate.update(
            self.num_vars - self.num_asserted_vars - self.num_eliminated_vars - self.trail.len(),
        );
    }

    debug_assert!(asg.q_head == 0 || asg.trail[asg.q_head - 1].var.assign.is_some());
    #[cfg(feature = "debug_propagation")]
    debug_assert!(self.q_head == 0 || self.trail[self.q_head - 1].var.is(FlagVar::PROPAGATED));
}

pub fn backtrack_sandbox<'a>(
    vars: &mut [Var],
    asg: &mut AssignStack<'a>,
    vam: &mut VarActivityManager,
) {
    if asg.trail_lim.is_empty() {
        return;
    }
    let lim = asg.trail_lim[asg.root_level as usize];
    for i in lim..asg.trail.len() {
        let l = asg.trail[i];
        let vi = l.var.id;
        debug_assert!(asg.root_level < l.var.level);
        l.var.assign = None;
        l.var.reason = AssignReason::None;
        vam.insert_heap(v);
    }
    asg.trail.truncate(lim);
    asg.trail_lim.truncate(asg.root_level as usize);
    asg.q_head = asg.trail.len();
}

/// UNIT PROPAGATION.
/// Note:
///  - *Precondition*: no checking dead clauses. They cause crash.
///  - This function assumes there's no dead clause.
///    So Eliminator should call `garbage_collect` before me.
///  - The order of literals in binary clauses will be modified to hold
///    propagation order.
pub fn propagate<'a>(
    vars: &'a mut [Var<'a>],
    asg: &'a mut AssignStack<'a>,
    vam: &'a mut VarActivityManager,
    cdb: &'a mut ClauseDB<'a>,
) -> PropagationResult<'a> {
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
            asg.dpc_ema.update(asg.num_decision);
            asg.ppc_ema.update(asg.num_propagation);
            asg.num_conflict += 1;
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
            if let cc @ Err(_) = asg.reuse_saved_trail(cdb) {
                asg.num_propagation += 1;
                asg.num_conflict += 1;
                asg.num_reconflict += 1;
                asg.dpc_ema.update(asg.num_decision);
                asg.ppc_ema.update(asg.num_propagation);
                return cc;
            }
        };
    }
    #[cfg(not(feature = "trail_saving"))]
    macro_rules! from_saved_trail {
        () => {};
    }

    let dl = asg.decision_level();
    from_saved_trail!();
    while let Some(p) = asg.trail.get(asg.q_head) {
        asg.num_propagation += 1;
        asg.q_head += 1;
        #[cfg(feature = "debug_propagation")]
        {
            assert!(!p.var.is(FlagVar::PROPAGATED));
            vars[p.var.id].turn_on(FlagVar::PROPAGATED);
        }
        let propagating = Lit::from(usize::from(*p));
        let false_lit = !*p;

        #[cfg(feature = "boundary_check")]
        {
            vars[p.var.id].propagated_at = asg.num_conflict;
            vars[p.var.id].state = VarState::Propagated(asg.num_conflict);
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
            debug_assert!(!blocker.var.is(FlagVar::ELIMINATED));
            debug_assert_ne!(blocker, false_lit);
            debug_assert_eq!(cdb[cid].len(), 2);
            match blocker.var.assign {
                Some(true) => (),
                Some(false) => {
                    check_in!(cid, Propagate::EmitConflict(asg.num_conflict + 1, blocker));
                    conflict_path!(blocker, minimized_reason!(propagating));
                }
                None => {
                    debug_assert!(cdb[cid].lit0() == false_lit || cdb[cid].lit1() == false_lit);
                    assign_by_implication(
                        vars,
                        asg,
                        vam,
                        blocker,
                        minimized_reason!(propagating),
                        #[cfg(feature = "chrono_BT")]
                        propagating.var.level,
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
            debug_assert!(!cached.var.is(FlagVar::ELIMINATED));
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
            let mut other_watch_value = cached.var.assign;
            let mut updated_cache: Option<Lit<'a>> = None;
            if Some(true) == other_watch_value {
                #[cfg(feature = "maintain_watch_cache")]
                debug_assert!(cdb[cid].lit0() == cached || cdb[cid].lit1() == cached);

                // In this path, we use only `AssignStack::assign`.
                // assert!(w.blocker == cdb[w.c].lits[0] || w.blocker == cdb[w.c].lits[1]);
                cdb.transform_by_restoring_watch_cache(propagating, &mut source, None);
                check_in!(cid, Propagate::CacheSatisfied(asg.num_conflict));
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
                    other_watch_value = other.var.assign;
                    if Some(true) == other_watch_value {
                        debug_assert!(!other.var.is(FlagVar::ELIMINATED));
                        // In this path, we use only `AssignStack::assign`.
                        cdb.transform_by_restoring_watch_cache(
                            propagating,
                            &mut source,
                            Some(other),
                        );
                        check_in!(cid, Propagate::CacheSatisfied(asg.num_conflict));
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
                    if lk.var.assign != Some(false) {
                        let new_watch = !*lk;
                        cdb.detach_watch_cache(propagating, &mut source);
                        cdb.transform_by_updating_watch(cid, false_watch_pos, k, true);
                        cdb[cid].search_from = (k + 1) as u16;
                        debug_assert_ne!(new_watch.assigned(), Some(true));
                        check_in!(
                            cid,
                            Propagate::FindNewWatch(asg.num_conflict, propagating, new_watch)
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
                check_in!(cid, Propagate::EmitConflict(asg.num_conflict + 1, cached));
                conflict_path!(cached, AssignReason::Implication(cid));
            }

            #[cfg(feature = "chrono_BT")]
            let dl = cdb[cid]
                .iter()
                .skip(1)
                .map(|l| l.var.level)
                .max()
                .unwrap_or(asg.root_level);

            debug_assert_eq!(cdb[cid].lit0(), cached);
            debug_assert_eq!(cached.assigned(), None);
            debug_assert!(other_watch_value.is_none());
            assign_by_implication(
                vars,
                asg,
                vam,
                heap,
                cached,
                AssignReason::Implication(cid),
                #[cfg(feature = "chrono_BT")]
                dl,
            );
            check_in!(cid, Propagate::BecameUnit(asg.num_conflict, cached));
        }
        from_saved_trail!();
    }
    let na = asg.q_head + asg.num_eliminated_vars + asg.num_asserted_vars;
    if asg.num_best_assign <= na && 0 < dl {
        asg.best_assign = true;
        asg.num_best_assign = na;
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
pub fn propagate_sandbox<'a>(
    vars: &'a mut [Var<'a>],
    asg: &'a mut AssignStack<'a>,
    vam: &'a mut VarActivityManager,
    cdb: &'a mut ClauseDB<'a>,
) -> PropagationResult<'a> {
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
    while let Some(p) = asg.trail.get(asg.q_head) {
        asg.q_head += 1;
        #[cfg(feature = "debug_propagation")]
        assert!(!self.var[p.vi()].is(Flag::PROPAGATED));
        #[cfg(feature = "debug_propagation")]
        vars[p.var.id].turn_on(Flag::PROPAGATED);
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
            debug_assert!(!blocker.var.is(FlagVar::ELIMINATED));
            debug_assert_ne!(blocker, false_lit);

            #[cfg(feature = "boundary_check")]
            debug_assert_eq!(cdb[*cid].len(), 2);

            match blocker.var.assign {
                Some(true) => (),
                Some(false) => conflict_path!(blocker, AssignReason::BinaryLink(propagating)),
                None => {
                    debug_assert!(cdb[cid].lit0() == false_lit || cdb[cid].lit1() == false_lit);

                    assign_by_implication(
                        vars,
                        asg,
                        vam,
                        blocker,
                        AssignReason::BinaryLink(propagating),
                        #[cfg(feature = "chrono_BT")]
                        false_lit.var.level,
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
            debug_assert!(!cached.var.is(FlagVar::ELIMINATED));
            let mut other_watch_value = cached.var.assign;
            let mut updated_cache: Option<Lit<'a>> = None;
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
                    other_watch_value = other.var.assign;
                    if Some(true) == other_watch_value {
                        debug_assert!(!cached.var.is(FlagVar::ELIMINATED));
                        cdb.transform_by_restoring_watch_cache(
                            propagating,
                            &mut source,
                            Some(other),
                        );
                        check_in!(cid, Propagate::SandboxCacheSatisfied(asg.num_conflict));
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
                    if lk.var.assign != Some(false) {
                        let new_watch = !*lk;
                        cdb.detach_watch_cache(propagating, &mut source);
                        cdb.transform_by_updating_watch(cid, false_watch_pos, k, true);
                        cdb[cid].search_from = (k as u16).saturating_add(1);
                        debug_assert!(
                            (!new_watch).assigned() == Some(true)
                                || (!new_watch).assigned().is_none()
                        );
                        check_in!(
                            cid,
                            Propagate::SandboxFindNewWatch(asg.num_conflict, false_lit, new_watch,)
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
                    Propagate::SandboxEmitConflict(asg.num_conflict, propagating)
                );
                return Err((cached, AssignReason::Implication(cid)));
            }

            #[cfg(feature = "chrono_BT")]
            let dl = cdb[cid]
                .iter()
                .skip(1)
                .map(|l| l.var.level)
                .max()
                .unwrap_or(asg.root_level);
            debug_assert_eq!(cdb[cid].lit0(), cached);
            debug_assert_eq!(cached.assigned(), None);
            debug_assert!(other_watch_value.is_none());

            assign_by_implication(
                vars,
                asg,
                vam,
                cached,
                AssignReason::Implication(cid),
                #[cfg(feature = "chrono_BT")]
                dl,
            );
            check_in!(cid, Propagate::SandboxBecameUnit(asg.num_conflict));
        }
    }
    Ok(())
}

pub fn clear_asserted_literals<'a>(
    vars: &'a mut [Var<'a>],
    asg: &'a mut AssignStack<'a>,
    vam: &'a mut VarActivityManager,
    cdb: &'a mut ClauseDB<'a>,
) -> MaybeInconsistent {
    debug_assert_eq!(asg.decision_level(), asg.root_level);
    loop {
        if asg.remains() {
            propagate_sandbox(vars, asg, vam, cdb).map_err(|_| SolverError::RootLevelConflict)?;
        }
        propagate_at_root_level(vars, asg, vam, cdb)?;
        if asg.remains() {
            propagate_sandbox(vars, asg, vam, cdb).map_err(|_| SolverError::RootLevelConflict)?;
        } else {
            break;
        }
    }
    // wipe asserted literals from trail and increment the number of asserted vars.
    asg.num_asserted_vars += asg.trail.len();
    asg.trail.clear();
    asg.q_head = 0;
    Ok(())
}

/// simplify clauses by propagating literals at root level.
fn propagate_at_root_level<'a, 'b>(
    _vars: &'a mut [Var<'a>],
    asg: &'a mut AssignStack<'a>,
    _vam: &'a mut VarActivityManager,
    cdb: &'b mut ClauseDB<'a>,
) -> MaybeInconsistent
where
    'b: 'a,
{
    let mut num_propagated = 0;
    while num_propagated < asg.trail.len() {
        num_propagated = asg.trail.len();
        let n = 100; // cdb.clause.len();
        for ci in 1..n {
            let cid = ClauseId::from(ci);
            // if cdb[cid].is_dead() {
            //     continue;
            // }
            // debug_assert!(cdb[cid].iter().all(|l| !l.var.is(FlagVar::ELIMINATED)));
            match cdb.transform_by_simplification(cid) {
                RefClause::Clause(_) => (),
                RefClause::Dead => (), // was a satisfied clause
                RefClause::EmptyClause => return Err(SolverError::EmptyClause),
                RefClause::RegisteredClause(_) => (),
                RefClause::UnitClause(_lit) => {
                    // debug_assert!(lit.assigned().is_none());
                    // cdb.certificate_add_assertion(lit);
                    // assign_at_root_level(vars, asg, heap, vam, lit)?;
                    // cdb.remove_clause(cid);
                }
            }
        }
    }
    Ok(())
}

impl AssignStack<'_> {
    /// save the current assignments as the best phases
    fn save_best_phases(&mut self) {
        #[cfg(feature = "best_phases_tracking")]
        {
            self.best_phases.clear();
            for l in self.trail.iter().skip(self.len_upto(self.root_level)) {
                let vi = l.var.id;
                if let Some(b) = l.var.assign {
                    self.best_phases.insert(vi, (b, l.var.reason));
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

#[allow(dead_code)]
fn check<'a>((b0, b1): (Lit<'a>, Lit<'a>)) {
    assert_ne!(b0.assigned(), Some(false));
    assert_ne!(b1.assigned(), Some(false));
}

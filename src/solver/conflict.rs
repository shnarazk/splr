//! Conflict Analysis

#[cfg(feature = "boundary_check")]
use crate::assign::DebugReportIF;

use {
    super::State,
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        types::*,
    },
};

/// returns:
/// - 0: if a new assigngment is generated by conflict analysis.
/// - 1: if a binary link generated
/// - otherwise: it's the LBD of the learnt clause.
#[allow(clippy::cognitive_complexity)]
pub fn handle_conflict(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    cc: &ConflictContext,
) -> Result<u16, SolverError> {
    #[cfg(feature = "chrono_BT")]
    let mut conflicting_level = asg.decision_level();
    #[cfg(not(feature = "chrono_BT"))]
    let conflicting_level = asg.decision_level();

    // we need a catch here for handling the possibility of level zero conflict
    // at higher level due to the incoherence between the current level and conflicting
    // level in chrono_BT. This leads to UNSAT solution. No need to update misc stats.
    {
        if let AssignReason::Implication(wli) = cc.1 {
            if cdb[wli.as_ci()].iter().all(|l| asg.level(l.vi()) == 0) {
                return Err(SolverError::RootLevelConflict(*cc));
            }
        }
    }

    // If we can settle this conflict w/o restart, solver will get a big progress.
    #[cfg(feature = "chrono_BT")]
    let chronobt = 1000 < asg.num_conflict && 0 < state.config.c_cbt_thr;
    #[cfg(not(feature = "chrono_BT"))]
    let chronobt: bool = false;

    #[cfg(feature = "chrono_BT")]
    {
        let c = match cc.1 {
            AssignReason::Implication(cid) => &cdb[cid],
            _ => panic!(),
        };
        let level = asg.level_ref();
        let max_level = c.iter().map(|l| level[l.vi()]).max().unwrap();

        if chronobt
            && state.config.c_cbt_thr < conflicting_level
            && 1 == c.iter().filter(|l| level[l.vi()] == max_level).count()
        {
            if let Some(second_level) = c
                .iter()
                .map(|l| level[l.vi()])
                .filter(|l| *l < max_level)
                .max()
            {
                debug_assert!(0 < second_level);
                asg.cancel_until(second_level);
                return Ok(());
            }
        }
        if max_level < conflicting_level {
            conflicting_level = max_level;
            asg.cancel_until(conflicting_level);
        }
    }

    asg.handle(SolverEvent::Conflict);

    state.derive20.clear();
    let assign_level = conflict_analyze(asg, cdb, state, cc).max(asg.root_level());
    let new_learnt = &mut state.new_learnt;
    let learnt_len = new_learnt.len();
    if learnt_len == 0 {
        #[cfg(feature = "boundary_check")]
        {
            println!(
                "empty learnt at {}({}) by {:?}",
                cl,
                asg.reason(asg.decision_vi(cl)).is_none(),
                asg.dump(asg, &cdb[ci]),
            );
        }
        return Err(SolverError::EmptyClause);
    }
    let l0 = new_learnt[0];
    if learnt_len == 1 {
        //
        //## A NEW ASSERTION by UNIT LEARNT CLAUSE GENERATION
        //
        match asg.assigned(l0) {
            Some(true) if asg.root_level() < asg.level(l0.vi()) => {
                panic!("double assignment occured");
                // asg.lift_to_asserted(l0.vi());
            }
            Some(false) if asg.level(l0.vi()) == asg.root_level() => {
                return Err(SolverError::RootLevelConflict((l0, asg.reason(l0.vi()))));
            }
            _ => {
                // dump to certified even if it's a literal.
                cdb.certificate_add_assertion(l0);
                if asg.assign_at_root_level(l0).is_err() {
                    unreachable!("handle_conflict::root_level_conflict_by_assertion");
                }
                let vi = l0.vi();
                state.restart.handle(SolverEvent::Assert(vi));
                cdb.handle(SolverEvent::Assert(vi));
                return Ok(0);
            }
        }
    }
    let l1 = new_learnt[1];
    // assert: root_level < cl, which was checked already by new_learnt.is_empty().

    // NCB places firstUIP on level bl, while CB does it on level cl.
    // ?? || Therefore the condition to use CB is: activity(firstUIP) < activity(v(bl)).
    // PREMISE: root_level < bl, because asg.decision_vi accepts only non-zero values.

    // At the present time, some reason clauses can contain first UIP or its negation.
    // So we have to filter vars instead of literals to avoid double counting.
    #[cfg(feature = "reason_side_rewarding")]
    let mut bumped = new_learnt.iter().map(|l| l.vi()).collect::<Vec<VarId>>();
    for lit in new_learnt.iter() {
        //
        //## Learnt Literal Rewarding
        //
        asg.reward_at_analysis(lit.vi());

        //
        //## Reason-Side Rewarding
        //
        #[cfg(feature = "reason_side_rewarding")]
        match asg.reason(lit.vi()) {
            AssignReason::BinaryLink(from) => {
                let vi = from.vi();
                if !bumped.contains(&vi) {
                    asg.reward_at_analysis(vi);
                    bumped.push(vi);
                }
            }
            AssignReason::Implication(r) => {
                for l in cdb[r.as_ci()].iter() {
                    let vi = l.vi();
                    if !bumped.contains(&vi) {
                        asg.reward_at_analysis(vi);
                        bumped.push(vi);
                    }
                }
            }
            AssignReason::Decision(lv) => {
                let vi = asg.decision_vi(lv);
                if !bumped.contains(&vi) {
                    asg.reward_at_analysis(vi);
                    bumped.push(vi);
                }
            }
            AssignReason::None => unreachable!("handle_conflict"),
        }
    }
    if chronobt && assign_level + state.config.c_cbt_thr <= conflicting_level {
        asg.cancel_until(conflicting_level - 1);
    } else {
        asg.cancel_until(assign_level);
    }
    debug_assert_eq!(asg.assigned(l0), None);
    debug_assert_eq!(
        new_learnt.iter().skip(1).map(|l| asg.level(l.vi())).max(),
        Some(assign_level)
    );
    let rank: u16;
    match cdb.new_clause(asg, new_learnt, true) {
        RefClause::Clause(cid) if learnt_len == 2 => {
            #[cfg(feature = "boundary_check")]
            cdb[cid].set_birth(asg.num_conflict);

            debug_assert_ne!(l0, Lit::default());
            debug_assert_ne!(l1, Lit::default());
            debug_assert_eq!(l0, cdb[cid].lit0());
            debug_assert_eq!(l1, cdb[cid].lit1());
            debug_assert_eq!(asg.assigned(l1), Some(false));
            debug_assert_eq!(asg.assigned(l0), None);

            asg.assign_by_implication(
                l0,
                AssignReason::BinaryLink(!l1),
                #[cfg(feature = "chrono_BT")]
                assign_level,
            );
            // || check_graph(asg, cdb, l0, "biclause");
            for cid in &state.derive20 {
                cdb[*cid].turn_on(FlagClause::DERIVE20);
            }
            rank = 1;
            #[cfg(feature = "bi_clause_completion")]
            cdb.complete_bi_clauses(asg);
        }
        RefClause::Clause(cid) => {
            #[cfg(feature = "boundary_check")]
            cdb[cid].set_birth(asg.num_conflict);

            debug_assert_eq!(cdb[cid].lit0(), l0);
            debug_assert_eq!(asg.assigned(l0), None);
            asg.assign_by_implication(
                l0,
                AssignReason::Implication(WatchLiteralIndex::new(cid, 0)),
                #[cfg(feature = "chrono_BT")]
                assign_level,
            );
            // || check_graph(asg, cdb, l0, "clause");
            rank = cdb[cid].rank;
            if rank <= 20 {
                for cid in &state.derive20 {
                    cdb[*cid].turn_on(FlagClause::DERIVE20);
                }
            }
        }
        RefClause::RegisteredClause(cid) => {
            debug_assert_eq!(learnt_len, 2);
            debug_assert!(
                (l0 == cdb[cid].lit0() && l1 == cdb[cid].lit1())
                    || (l0 == cdb[cid].lit1() && l1 == cdb[cid].lit0())
            );
            debug_assert_eq!(asg.assigned(l1), Some(false));
            debug_assert_eq!(asg.assigned(l0), None);
            rank = 1;
            asg.assign_by_implication(
                l0,
                AssignReason::BinaryLink(!l1),
                #[cfg(feature = "chrono_BT")]
                assign_level,
            );
            // || check_graph(asg, cdb, l0, "registeredclause");
        }
        RefClause::Dead => unreachable!("handle_conflict::RefClause::Deaf"),
        RefClause::EmptyClause => unreachable!("handel_conflict::RefClause::EmptyClause"),
        RefClause::UnitClause(_) => unreachable!("handle_conflict::RefClause::UnitClause"),
    }
    state.c_lvl.update(conflicting_level as f64);
    state.b_lvl.update(assign_level as f64);
    state
        .e_mode
        .update(conflicting_level as f64 - assign_level as f64);
    state.derive20.clear();
    Ok(rank)
}

///
/// ## Conflict Analysis
///
fn conflict_analyze(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    cc: &ConflictContext,
) -> DecisionLevel {
    let learnt = &mut state.new_learnt;
    learnt.clear();
    learnt.push(Lit::from(u32::MAX));
    let root_level = asg.root_level();
    let dl = asg.decision_level();
    let mut path_cnt = 0;
    let (mut p, mut reason) = cc;
    let mut deep_path_cnt = 0;
    let mut reason_side_lits: Vec<Lit> = Vec::new();

    macro_rules! new_depend_on_conflict_level {
        ($vi: expr) => {
            path_cnt += 1;
            //## Conflict-Side Rewarding
            asg.reward_at_analysis($vi);
        };
    }
    macro_rules! trace {
        ($($arg: expr),*) => {
            #[cfg(feature = "trace_analysis")]
            println!($($arg),*);
        };
    }
    macro_rules! trace_lit {
        ($lit: expr, $message: expr) => {
            #[cfg(feature = "trace_analysis")]
            {
                let vi = $lit.vi();
                let lv = asg.level(vi);
                println!("{}: literal {} at level {}", $message, i32::from($lit), lv);
            }
        };
    }
    macro_rules! validate_vi {
        ($vi: expr) => {
            debug_assert!(!asg.var($vi).is(FlagVar::ELIMINATED));
            debug_assert!(asg.assign($vi).is_some());
            debug_assert!(asg.level($vi) <= dl);
        };
    }
    macro_rules! set_seen {
        ($vi: expr) => {
            debug_assert!(!asg.var($vi).is(FlagVar::CA_SEEN));
            asg.var_mut($vi).turn_on(FlagVar::CA_SEEN);
        };
    }
    macro_rules! boundary_check {
        ($condition: expr, $($arg: expr),+) => {
            #[cfg(feature = "boundary_check")]
            {
                if !$condition {
                    dbg!(cc);
                    dbg!(dl);
                    tracer(asg, cdb);
                    println!("Learnt clause so far: {}",
                             learnt.report(asg)
                             .iter()
                             .map(|r| format!("  {:?}", r))
                             .collect::<Vec<String>>()
                             .join("\n")
                    );
                    panic!($($arg),*);
                }
            }
        };
    }

    {
        trace_lit!(p, "- handle conflicting literal");
        let vi = p.vi();
        asg.reward_at_analysis(vi);
        debug_assert_ne!(asg.assign(vi), None);
        validate_vi!(vi);
        set_seen!(vi);
        let lvl = asg.level(vi);
        if dl == lvl {
            new_depend_on_conflict_level!(vi);
        } else {
            debug_assert_ne!(root_level, lvl);
            learnt.push(p);
            if asg.decision_vi(lvl) != vi {
                deep_path_cnt += 1;
                reason_side_lits.push(p);
            }
        }
    }
    let mut trail_index = asg.stack_len() - 1;
    let mut max_lbd: u16 = 0;
    let mut ci_with_max_lbd: Option<ClauseIndex> = None;
    #[cfg(feature = "trace_analysis")]
    println!("##################");
    loop {
        match reason {
            AssignReason::BinaryLink(l) => {
                let vi = l.vi();
                if !asg.var(vi).is(FlagVar::CA_SEEN) {
                    validate_vi!(vi);
                    debug_assert_eq!(asg.level(vi), dl, "strange level binary clause");
                    // if root_level == asg.level(vi) { continue; }
                    set_seen!(vi);
                    trace_lit!(l, " - binary linked");
                    new_depend_on_conflict_level!(vi);
                }
            }
            AssignReason::Implication(wli) => {
                trace!(
                    "analyze clause {}(first literal: {}) for {}",
                    cid,
                    i32::from(cdb[wli.as_ci()].lit0()),
                    p
                );
                debug_assert!(2 < cdb[wli.as_ci()].len());
                // if !cdb.update_at_analysis(asg, cid) {
                let ci = wli.as_ci();
                if !cdb[ci].is(FlagClause::LEARNT) {
                    state.derive20.push(ci);
                }
                if max_lbd < cdb[ci].rank {
                    max_lbd = cdb[ci].rank;
                    ci_with_max_lbd = Some(ci);
                }
                assert_eq!(
                    p,
                    cdb[wli],
                    "At level {}, broken implication chain from {:?}@{} to {:?}{:?}",
                    asg.decision_level(),
                    p,
                    asg.level(p.vi()),
                    wli,
                    &cdb[wli],
                );
                let skip = wli.as_wi();
                #[cfg(feature = "trace_analysis")]
                if skip == 1 {
                    trace!(
                        "AMEND: analyze disordered clause {}{:?}(second literal: {}) for {}",
                        ci,
                        cdb[ci],
                        i32::from(cdb[ci].lit1()),
                        p
                    );
                }
                for (i, q) in cdb[ci].iter().enumerate() {
                    if i == skip {
                        continue;
                    }
                    let vi = q.vi();
                    validate_vi!(vi);
                    if !asg.var(vi).is(FlagVar::CA_SEEN) {
                        let lvl = asg.level(vi);
                        if root_level == lvl {
                            trace_lit!(q, " -- ignore");
                            continue;
                        }
                        set_seen!(vi);
                        if dl == lvl {
                            trace_lit!(q, " -- found another path");
                            new_depend_on_conflict_level!(vi);
                        } else {
                            trace_lit!(q, " -- push to learnt");
                            learnt.push(*q);
                            if asg.decision_vi(lvl) != vi && !reason_side_lits.contains(q) {
                                deep_path_cnt += 1;
                                reason_side_lits.push(*q);
                            }
                        }
                    } else {
                        trace!("{:?} -- ignore flagged already", q);
                    }
                }
            }
            AssignReason::Decision(_) | AssignReason::None => {
                boundary_check!(
                    false,
                    "found a strange var {:?}:: path_cnt {}\nDecisionMap\n{}",
                    reason,
                    path_cnt,
                    asg.stack_iter()
                        .skip(trail_index)
                        .filter(|l| matches!(asg.reason(l.vi()), AssignReason::Decision(_)))
                        .map(|l| format!("{:?}", l.report(asg)))
                        .collect::<Vec<String>>()
                        .join("\n")
                );
            }
        }
        //
        // set the index of the next literal to trail_index
        //
        #[allow(clippy::blocks_in_conditions)]
        while {
            let vi = asg.stack(trail_index).vi();
            boundary_check!(
                0 < vi && vi < asg.level_ref().len(),
                "trail[{}] has an invalid var index {}",
                trail_index,
                asg.stack(trail_index)
            );
            let lvl = asg.level(vi);
            let v = asg.var(vi);
            !v.is(FlagVar::CA_SEEN) || lvl != dl
        } {
            trace_lit!(asg.stack(trail_index), "skip, not flagged");
            boundary_check!(
                0 < trail_index,
                "Broke the bottom:: path_cnt {} scanned to {}",
                path_cnt,
                asg.stack_len() - trail_index
            );
            trail_index -= 1;
        }
        p = asg.stack(trail_index);
        trace!("move to flagged {}; num path: {}", p.vi(), path_cnt - 1);

        asg.var_mut(p.vi()).turn_off(FlagVar::CA_SEEN);
        // since the trail can contain a literal which level is under `dl` after
        // the `dl`-th decision var, we must skip it.
        path_cnt -= 1;
        if path_cnt == 0 {
            break;
        }
        debug_assert!(0 < trail_index);
        trail_index -= 1;
        reason = asg.reason(p.vi());
    }
    if let Some(cid) = ci_with_max_lbd {
        cdb.update_at_analysis(asg, cid);
    }
    // debug_assert!(learnt.iter().all(|l| *l != !p));
    debug_assert_eq!(asg.level(p.vi()), dl);
    learnt[0] = !p;
    trace!(
        "appending {}, the final (but not minimized) learnt is {:?}",
        learnt[0],
        learnt
    );
    // deep_trace
    if false {
        macro_rules! set_seen2 {
            ($vi: expr) => {
                debug_assert!(!asg.var($vi).is(FlagVar::CA_SEEN2));
                asg.var_mut($vi).turn_on(FlagVar::CA_SEEN2);
            };
        }
        reason_side_lits.iter().for_each(|l| {
            /* assert!(0 < asg.level(l.vi()));
            assert!(
                !asg.var(l.vi()).is(FlagVar::CA_SEEN),
                "l:{} in {:?}\n{:?}\nlevel: {}\n{:?}",
                l,
                asg.var(l.vi()),
                reason_side_lits,
                asg.decision_level(),
                asg.stack_iter().collect::<Vec<_>>(),
            ); */
            set_seen2!(l.vi());
        });
        // assert_eq!(deep_path_cnt, reason_side_lits.len());
        for ti in (asg.len_upto(root_level)..trail_index).rev() {
            let p: Lit = asg.stack(ti);
            let vi = p.vi();
            if !asg.var(vi).is(FlagVar::CA_SEEN2) {
                continue;
            }
            asg.var_mut(p.vi()).turn_off(FlagVar::CA_SEEN2);
            match asg.reason(p.vi()) {
                AssignReason::BinaryLink(l) => {
                    let vi = l.vi();
                    if !asg.var(vi).is(FlagVar::CA_SEEN2) && root_level < asg.level(vi) {
                        // validate_vi!(vi);
                        set_seen2!(vi);
                        deep_path_cnt += 1;
                    }
                }
                AssignReason::Implication(wli) => {
                    let (ci, skip) = wli.indices();
                    for (i, q) in cdb[ci].iter().enumerate() {
                        if i == skip {
                            continue;
                        }
                        let vi = q.vi();
                        // validate_vi!(vi);
                        if !asg.var(vi).is(FlagVar::CA_SEEN2) && root_level < asg.level(vi) {
                            set_seen2!(vi);
                            deep_path_cnt += 1;
                        }
                    }
                }
                AssignReason::Decision(lv) => {
                    if 0 < lv {
                        let vi = asg.decision_vi(lv);
                        asg.reward_at_analysis(vi);
                    }
                }
                AssignReason::None => unreachable!(),
            }
            deep_path_cnt -= 1;
            if deep_path_cnt == 0 {
                break;
            }
        }
        // assert_eq!(0, deep_path_cnt);
        // for i in 0..asg.len_upto(root_level) {
        //     assert!(!asg.var(asg.stack(i).vi()).is(FlagVar::CA_SEEN2));
        // }
        /* for i in 0..asg.stack_len() {
            assert!(
                !asg.var(asg.stack(i).vi()).is(FlagVar::CA_SEEN),
                "{} at {}: level: {} is CA_SEEN",
                asg.stack(i),
                i,
                asg.level(asg.stack(i).vi())
            );
        } */
    }
    minimize_learnt(&mut state.new_learnt, asg, cdb)
}

fn minimize_learnt(
    new_learnt: &mut Vec<Lit>,
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
) -> DecisionLevel {
    let mut to_clear: Vec<Lit> = vec![new_learnt[0]];
    debug_assert!(asg.assign(new_learnt[0].vi()).is_some());
    let mut levels = vec![false; asg.decision_level() as usize + 1];
    for l in &new_learnt[1..] {
        to_clear.push(*l);
        levels[asg.level(l.vi()) as usize] = true;
    }
    let l0 = new_learnt[0];
    new_learnt.retain(|l| *l == l0 || !l.is_redundant(asg, cdb, &mut to_clear, &levels));
    if 1 < new_learnt.len() {
        cdb.minimize_with_bi_clauses(asg, new_learnt);
    }
    // find correct backtrack level from remaining literals
    let mut level_to_return = 0;
    if 1 < new_learnt.len() {
        let mut max_i = 1;
        level_to_return = asg.level(new_learnt[max_i].vi());
        for (i, l) in new_learnt.iter().enumerate().skip(2) {
            let lv = asg.level(l.vi());
            if level_to_return < lv {
                level_to_return = lv;
                max_i = i;
            }
        }
        new_learnt.swap(1, max_i);
    }
    for l in &to_clear {
        asg.var_mut(l.vi()).turn_off(FlagVar::CA_SEEN);
    }
    level_to_return
}

/// return `true` if the `lit` is redundant, which is defined by
/// any leaf of implication graph for it isn't an asserted var nor a decision var.
impl Lit {
    fn is_redundant(
        self,
        asg: &mut AssignStack,
        cdb: &ClauseDB,
        clear: &mut Vec<Lit>,
        levels: &[bool],
    ) -> bool {
        if matches!(asg.reason(self.vi()), AssignReason::Decision(_)) {
            return false;
        }
        let mut stack = vec![self];
        let top = clear.len();
        while let Some(sl) = stack.pop() {
            match asg.reason(sl.vi()) {
                AssignReason::BinaryLink(l) => {
                    let vi = l.vi();
                    let lv = asg.level(vi);
                    if 0 < lv && !asg.var(vi).is(FlagVar::CA_SEEN) {
                        // if asg.reason(vi) != AssignReason::Decision(_) && levels[lv as usize] {
                        if matches!(
                            asg.reason(vi),
                            AssignReason::Implication(_) | AssignReason::BinaryLink(_)
                        ) && levels[lv as usize]
                        {
                            asg.var_mut(vi).turn_on(FlagVar::CA_SEEN);
                            stack.push(l);
                            clear.push(l);
                        } else {
                            // one of the roots is a decision var at an unchecked level.
                            for l in &clear[top..] {
                                asg.var_mut(l.vi()).turn_off(FlagVar::CA_SEEN);
                            }
                            clear.truncate(top);
                            return false;
                        }
                    }
                }
                AssignReason::Implication(wli) => {
                    let c = &cdb[wli.as_ci()];
                    let skip = wli.as_wi();
                    for (i, q) in c.iter().enumerate() {
                        if skip == i {
                            continue;
                        }
                        let vi = q.vi();
                        let lv = asg.level(vi);
                        if 0 < lv && !asg.var(vi).is(FlagVar::CA_SEEN) {
                            // if asg.reason(vi) != AssignReason::default() && levels[lv as usize] {
                            if matches!(
                                asg.reason(vi),
                                AssignReason::BinaryLink(_) | AssignReason::Implication(_)
                            ) && levels[lv as usize]
                            {
                                asg.var_mut(vi).turn_on(FlagVar::CA_SEEN);
                                stack.push(*q);
                                clear.push(*q);
                            } else {
                                // one of the roots is a decision var at an unchecked level.
                                for l in &clear[top..] {
                                    asg.var_mut(l.vi()).turn_off(FlagVar::CA_SEEN);
                                }
                                clear.truncate(top);
                                return false;
                            }
                        }
                    }
                }
                AssignReason::Decision(_) | AssignReason::None => unreachable!("is_redundant"),
            }
        }
        true
    }
}

#[allow(dead_code)]
fn check_graph(asg: &AssignStack, cdb: &ClauseDB, lit: Lit, mes: &str) {
    let its_level = asg.level(lit.vi());
    let mut children = Vec::new();
    let precedents = lit_level(asg, cdb, lit, &mut children, mes);
    assert!(precedents <= its_level);
}

#[allow(dead_code)]
fn lit_level(
    asg: &AssignStack,
    cdb: &ClauseDB,
    lit: Lit,
    bag: &mut Vec<Lit>,
    _mes: &str,
) -> DecisionLevel {
    if bag.contains(&lit) {
        return 0;
    }
    bag.push(lit);
    match asg.reason(lit.vi()) {
        AssignReason::Decision(0) => asg.root_level(),
        AssignReason::Decision(lvl) => lvl,
        AssignReason::Implication(wli) => {
            assert_eq!(
                cdb[wli.as_ci()].lit0(),
                lit,
                "lit0 {} != lit{}, cid {}, {}",
                cdb[wli.as_ci()].lit0(),
                lit,
                wli.as_ci(),
                &cdb[wli]
            );
            // assert!(
            //     !bag.contains(&lit),
            //     "{}; {} is contained in {:?}\n{:?}\n{}",
            //     mes,
            //     lit,
            //     bag,
            //     asg.reason(lit.vi()),
            //     dumper(asg, cdb, bag),
            // );
            // bag.push(lit);
            cdb[wli.as_ci()]
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != wli.as_wi())
                .map(|(_, l)| lit_level(asg, cdb, !*l, bag, _mes))
                .max()
                .unwrap()
        }
        AssignReason::BinaryLink(b) => lit_level(asg, cdb, b, bag, _mes),
        AssignReason::None => panic!("One of root of {lit} isn't assigned."),
    }
}

#[allow(dead_code)]
fn dumper(asg: &AssignStack, cdb: &ClauseDB, bag: &[Lit]) -> String {
    use std::fmt::Write as _;
    let mut s = String::new();
    for l in bag {
        writeln!(
            s,
            "{:8>} :: level {:4>}, {:?} {:?}",
            *l,
            asg.level(l.vi()),
            asg.reason(l.vi()),
            match asg.reason(l.vi()) {
                AssignReason::Decision(_) => vec![],
                AssignReason::BinaryLink(lit) => vec![*l, !lit],
                AssignReason::Implication(wli) =>
                    cdb[wli.as_ci()].iter().copied().collect::<Vec<Lit>>(),
                AssignReason::None => vec![],
            },
        )
        .unwrap();
    }
    s
}

#[cfg(feature = "boundary_check")]
fn tracer(asg: &AssignStack, cdb: &ClauseDB) {
    use std::io::{self, Write};
    loop {
        let mut input = String::new();
        print!("cid(or 0 for quit): ");
        std::io::stdout().flush().expect("IO error");
        io::stdin().read_line(&mut input).expect("IO error");
        if input.is_empty() {
            break;
        }
        let Ok(cid) = input.trim().parse::<usize>() else {
            continue;
        };
        if cid == 0 {
            break;
        }
        println!(
            "{}",
            cdb[ClauseId::from(cid)]
                .report(asg)
                .iter()
                .map(|r| format!(
                    " {}{:?}",
                    asg.var(Lit::from(r.lit).vi())
                        .is(FlagVar::CA_SEEN)
                        .then(|| "S")
                        .unwrap_or(" "),
                    r
                ))
                .collect::<Vec<String>>()
                .join("\n"),
        );
    }
    panic!("done");
}

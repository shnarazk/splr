//! Conflict Analysis

#[cfg(feature = "boundary_check")]
use crate::assign::DebugReportIF;

use {
    super::{
        restart::{ProgressUpdate, RestartIF, Restarter},
        State,
    },
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        solver::SolverEvent,
        types::*,
    },
};

#[allow(clippy::cognitive_complexity)]
pub fn handle_conflict(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    rst: &mut Restarter,
    state: &mut State,
    cc: &ConflictContext,
) -> MaybeInconsistent {
    #[cfg(feature = "chrono_BT")]
    let mut conflicting_level = asg.decision_level();
    #[cfg(not(feature = "chrono_BT"))]
    let conflicting_level = asg.decision_level();

    // we need a catch here for handling the possibility of level zero conflict
    // at higher level due to the incoherence between the current level and conflicting
    // level in chronoBT. This leads to UNSAT solution. No need to update misc stats.
    {
        let level = asg.level_ref();
        if let AssignReason::Implication(cid) = cc.1 {
            if cdb[cid].iter().all(|l| level[l.vi()] == 0) {
                return Err(SolverError::RootLevelConflict(*cc));
            }
        }
    }

    // If we can settle this conflict w/o restart, solver will get a big progress.
    #[cfg(feature = "chrono_BT")]
    let chronobt = 1000 < asg.num_conflict && 0 < state.config.c_cbt_thr;
    #[cfg(not(feature = "chrono_BT"))]
    let chronobt: bool = false;

    rst.update(ProgressUpdate::Counter);
    // rst.block_restart(); // to update asg progress_evaluator

    #[cfg(feature = "chrono_BT")]
    {
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
                assert!(0 < second_level);
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
        #[cfg(debug)]
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
                    panic!("impossible inconsistency");
                }
                rst.handle(SolverEvent::Assert(l0.vi()));
                return Ok(());
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
                for l in cdb[r].iter() {
                    let vi = l.vi();
                    if !bumped.contains(&vi) {
                        asg.reward_at_analysis(vi);
                        bumped.push(vi);
                    }
                }
            }
            _ => (),
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
    match cdb.new_clause(asg, new_learnt, true) {
        RefClause::Clause(cid) if learnt_len == 2 => {
            #[cfg(feature = "boundary_check")]
            cdb[cid].set_birth(asg.num_conflict);

            debug_assert_eq!(l0, cdb[cid].lit0());
            debug_assert_eq!(l1, cdb[cid].lit1());
            debug_assert_eq!(asg.assigned(l1), Some(false));
            debug_assert_eq!(asg.assigned(l0), None);

            #[cfg(feature = "chrono_BT")]
            asg.assign_by_implication(l0, assign_level, cid, !l1);
            #[cfg(not(feature = "chrono_BT"))]
            asg.assign_by_implication(l0, AssignReason::BinaryLink(!l1));

            // || check_graph(asg, cdb, l0, "biclause");
            rst.update(ProgressUpdate::LBD(1));
            for cid in &state.derive20 {
                cdb[cid].turn_on(Flag::DERIVE20);
            }
            #[cfg(feature = "bi_clause_completion")]
            cdb.complete_bi_clauses(asg);
        }
        RefClause::Clause(cid) => {
            #[cfg(feature = "boundary_check")]
            cdb[cid].set_birth(asg.num_conflict);

            debug_assert_eq!(cdb[cid].lit0(), l0);
            debug_assert_eq!(asg.assigned(l0), None);

            #[cfg(feature = "chrono_BT")]
            asg.assign_by_implication(l0, assign_level, cid, NULL_LIT);
            #[cfg(not(feature = "chrono_BT"))]
            asg.assign_by_implication(l0, AssignReason::Implication(cid));

            // || check_graph(asg, cdb, l0, "clause");
            let lbd = cdb[cid].rank;
            rst.update(ProgressUpdate::LBD(lbd));
            if lbd <= 20 {
                for cid in &state.derive20 {
                    cdb[cid].turn_on(Flag::DERIVE20);
                }
            }
        }
        RefClause::Dead => panic!("impossible"),
        RefClause::EmptyClause => panic!("impossible"),
        RefClause::RegisteredClause(cid) => {
            debug_assert_eq!(learnt_len, 2);
            debug_assert!(
                (l0 == cdb[cid].lit0() && l1 == cdb[cid].lit1())
                    || (l0 == cdb[cid].lit1() && l1 == cdb[cid].lit0())
            );
            debug_assert_eq!(asg.assigned(l1), Some(false));
            debug_assert_eq!(asg.assigned(l0), None);

            #[cfg(feature = "chrono_BT")]
            asg.assign_by_implication(l0, assign_level, cid, !l1);
            #[cfg(not(feature = "chrono_BT"))]
            asg.assign_by_implication(l0, AssignReason::BinaryLink(!l1));

            // || check_graph(asg, cdb, l0, "registeredclause");
        }
        RefClause::UnitClause(_) => panic!("impossible"),
    }
    state.c_lvl.update(conflicting_level as f64);
    state.b_lvl.update(assign_level as f64);
    state.derive20.clear();
    Ok(())
}

///
/// ## Conflict Analysis
///
#[allow(clippy::cognitive_complexity)]
fn conflict_analyze(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    cc: &ConflictContext,
) -> DecisionLevel {
    let learnt = &mut state.new_learnt;
    learnt.clear();
    learnt.push(NULL_LIT);
    let root_level = asg.root_level();
    let dl = asg.decision_level();
    let mut path_cnt = 0;
    let (mut p, mut reason) = cc;
    {
        #[cfg(feature = "trace_analysis")]
        println!("- handle conflicting literal {}", p);

        let vi = p.vi();
        debug_assert!(!asg.var(vi).is(Flag::CA_SEEN) && !asg.var(vi).is(Flag::ELIMINATED));
        asg.var_mut(vi).turn_on(Flag::CA_SEEN);
        let lvl = asg.level(vi);
        debug_assert_ne!(root_level, lvl);
        if dl == lvl {
            path_cnt += 1;
            #[cfg(feature = "conflict_side_rewarding")]
            asg.reward_at_analysis(vi);
        } else {
            debug_assert!(lvl < dl);
            learnt.push(p);
        }
    }
    let mut ti = asg.stack_len() - 1; // trail index
    loop {
        match reason {
            AssignReason::BinaryLink(l) => {
                let vi = l.vi();
                if !asg.var(vi).is(Flag::CA_SEEN) {
                    assert_eq!(asg.level(vi), dl, "strange level binary clause");
                    // if root_level == asg.level(vi) { continue; }
                    debug_assert!(!asg.var(vi).is(Flag::ELIMINATED));
                    debug_assert!(asg.assign(vi).is_some());
                    asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                    path_cnt += 1;
                    #[cfg(feature = "conflict_side_rewarding")]
                    asg.reward_at_analysis(vi);
                }
            }
            AssignReason::Implication(cid) => {
                #[cfg(feature = "trace_analysis")]
                println!("analyze clause {} for {}", cid, p);

                cdb.mark_clause_as_used(asg, cid);
                if cdb[cid].is(Flag::LEARNT) {
                    cdb.reward_at_analysis(cid);
                } else {
                    state.derive20.push(cid);
                }
                cdb.lbd_of_dp_ema.update(cdb[cid].rank as f64);
                let c = &cdb[cid];
                debug_assert!(!c.is_dead());

                #[cfg(feature = "boundary_check")]
                assert!(2 < c.len());

                for q in &c[1..] {
                    let vi = q.vi();
                    if !asg.var(vi).is(Flag::CA_SEEN) {
                        let lvl = asg.level(vi);
                        if root_level == lvl {
                            continue;
                        }
                        debug_assert!(!asg.var(vi).is(Flag::ELIMINATED));
                        debug_assert!(
                            asg.assign(vi).is_some(),
                            "conflict_analysis found V{} {}",
                            vi,
                            asg.reason(vi),
                        );
                        debug_assert!(lvl <= dl);
                        asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                        if dl == lvl {
                            // println!("- flag for {} which level is {}", q.int(), lvl);
                            path_cnt += 1;

                            #[cfg(feature = "conflict_side_rewarding")]
                            asg.reward_at_analysis(vi);
                        } else {
                            #[cfg(feature = "trace_analysis")]
                            println!("- push {} to learnt, which level is {}", q, lvl);

                            learnt.push(*q);
                        }
                    } else {
                        #[cfg(feature = "trace_analysis")]
                        if !asg.var(vi).is(Flag::CA_SEEN) {
                            println!("- ignore {} because it was flagged", q);
                        } else {
                            println!("- ignore {} because its level is {}", q, asg.level(vi));
                        }
                    }
                }
            }
            AssignReason::Decision(_) | AssignReason::None => {
                #[cfg(feature = "boundary_check")]
                println!(
                    "conflict_analyze: faced a strange var {:?}:: path_cnt {} at level {}\nconflict\n  {:?}\nDecisionMap\n{}\nbuliding learnt\n{}\n",
                    reason,
                    path_cnt,
                    asg.decision_level(),
                    cc,
                    asg.stack_iter().skip(ti).filter(|l| matches!(asg.reason(l.vi()), AssignReason::Decision(_)))
                        .map(|l| format!("{:?}", l.report(asg)))
                        .collect::<Vec<String>>()
                        .join("\n"),
                    learnt.report(asg)
                        .iter()
                        .map(|r| format!("  {:?}", r))
                        .collect::<Vec<String>>()
                        .join("\n",),
                );
                #[cfg(feature = "boundary_check")]
                tracer(asg, cdb);
            }
        }
        // The following case was subsumed into `search`.
        /*
        // In an unsat problem, a conflict can occur at decision level zero
        // by a clause which literals' levels are zero.
        // So we have the possibility getting the following situation.
        if p == NULL_LIT && path_cnt == 0 {
            #[cfg(feature = "boundary_check")]
            println!("Empty learnt at lvl:{}", asg.level());
            learnt.clear();
            return asg.root_level;
        }
         */
        // set the index of the next literal to ti
        while {
            let vi = asg.stack(ti).vi();

            #[cfg(feature = "boundary_check")]
            if asg.level_ref().len() <= vi {
                panic!("ti:{}, lit:{}, len:{}", ti, asg.stack(ti), asg.stack_len());
            }

            let lvl = asg.level(vi);
            let v = asg.var(vi);
            !v.is(Flag::CA_SEEN) || lvl != dl
        } {
            #[cfg(feature = "trace_analysis")]
            println!("- skip {} because it isn't flagged", asg.stack(ti));

            #[cfg(feature = "boundary_check")]
            if 0 == ti {
                println!(
                    "conflict_analysis broke the bottom:: path_cnt {} scanned len {}, conflict level {}\nconflict {:?}\nbuilding learnt\n{}",
                    path_cnt,
                    asg.stack_len() - ti, // .report(asg),
                    dl,
                    cc,
                    learnt.report(asg)
                        .iter()
                        .map(|r| format!("  {:?}", r))
                        .collect::<Vec<String>>()
                        .join("\n"),
                );
                tracer(asg, cdb);
            }

            ti -= 1;
        }
        p = asg.stack(ti);

        #[cfg(feature = "trace_analysis")]
        println!("- move to flagged {}; num path: {}", p.vi(), path_cnt - 1,);

        asg.var_mut(p.vi()).turn_off(Flag::CA_SEEN);
        // since the trail can contain a literal which level is under `dl` after
        // the `dl`-th decision var, we must skip it.
        path_cnt -= 1;
        if path_cnt == 0 {
            break;
        }
        debug_assert!(0 < ti);
        ti -= 1;
        reason = asg.reason(p.vi());
    }
    debug_assert!(learnt.iter().all(|l| *l != !p));
    debug_assert_eq!(asg.level(p.vi()), dl);
    learnt[0] = !p;

    #[cfg(feature = "trace_analysis")]
    println!("- appending {}, the result is {:?}", learnt[0], learnt);

    state.minimize_learnt(asg, cdb)
}

impl State {
    fn minimize_learnt(&mut self, asg: &mut AssignStack, cdb: &mut ClauseDB) -> DecisionLevel {
        let State {
            ref mut new_learnt, ..
        } = self;
        let mut to_clear: Vec<Lit> = vec![new_learnt[0]];
        let mut levels = vec![false; asg.decision_level() as usize + 1];
        let level = asg.level_ref();
        for l in &new_learnt[1..] {
            to_clear.push(*l);
            levels[level[l.vi()] as usize] = true;
        }
        let l0 = new_learnt[0];

        #[cfg(feature = "boundary_check")]
        debug_assert!(!new_learnt.is_empty());

        new_learnt.retain(|l| *l == l0 || !l.is_redundant(asg, cdb, &mut to_clear, &levels));
        let len = new_learnt.len();
        if 2 < len && len < 30 {
            cdb.minimize_with_bi_clauses(asg, new_learnt);
        }
        // find correct backtrack level from remaining literals
        let mut level_to_return = 0;
        let level = asg.level_ref();
        if 1 < new_learnt.len() {
            let mut max_i = 1;
            level_to_return = level[new_learnt[max_i].vi()];
            for (i, l) in new_learnt.iter().enumerate().skip(2) {
                let lv = level[l.vi()];
                if level_to_return < lv {
                    level_to_return = lv;
                    max_i = i;
                }
            }
            new_learnt.swap(1, max_i);
        }
        for l in &to_clear {
            asg.var_mut(l.vi()).turn_off(Flag::CA_SEEN);
        }
        level_to_return
    }
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
        if let AssignReason::Decision(_) = asg.reason(self.vi()) {
            return false;
        }
        let mut stack = vec![self];
        let top = clear.len();
        while let Some(sl) = stack.pop() {
            match asg.reason(sl.vi()) {
                AssignReason::Decision(_) => panic!("no idea"),
                AssignReason::BinaryLink(l) => {
                    let vi = l.vi();
                    let lv = asg.level(vi);
                    if 0 < lv && !asg.var(vi).is(Flag::CA_SEEN) {
                        // if asg.reason(vi) != AssignReason::Decision(_) && levels[lv as usize] {
                        if matches!(
                            asg.reason(vi),
                            AssignReason::Implication(_) | AssignReason::BinaryLink(_)
                        ) && levels[lv as usize]
                        {
                            asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                            stack.push(l);
                            clear.push(l);
                        } else {
                            // one of the roots is a decision var at an unchecked level.
                            for l in &clear[top..] {
                                asg.var_mut(l.vi()).turn_off(Flag::CA_SEEN);
                            }
                            clear.truncate(top);
                            return false;
                        }
                    }
                }
                AssignReason::Implication(cid) => {
                    let c = &cdb[cid];

                    #[cfg(feature = "boundary_check")]
                    debug_assert!(0 < c.len());

                    for q in &(*c)[1..] {
                        let vi = q.vi();
                        let lv = asg.level(vi);
                        if 0 < lv && !asg.var(vi).is(Flag::CA_SEEN) {
                            // if asg.reason(vi) != AssignReason::default() && levels[lv as usize] {
                            if matches!(
                                asg.reason(vi),
                                AssignReason::BinaryLink(_) | AssignReason::Implication(_)
                            ) && levels[lv as usize]
                            {
                                asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                                stack.push(*q);
                                clear.push(*q);
                            } else {
                                // one of the roots is a decision var at an unchecked level.
                                for l in &clear[top..] {
                                    asg.var_mut(l.vi()).turn_off(Flag::CA_SEEN);
                                }
                                clear.truncate(top);
                                return false;
                            }
                        }
                    }
                }
                AssignReason::None => panic!("no idea"),
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
    mes: &str,
) -> DecisionLevel {
    if bag.contains(&lit) {
        return 0;
    }
    bag.push(lit);
    match asg.reason(lit.vi()) {
        AssignReason::Decision(0) => asg.root_level(),
        AssignReason::Decision(lvl) => lvl,
        AssignReason::Implication(cid) => {
            assert_eq!(
                cdb[cid].lit0(),
                lit,
                "lit0 {} != lit{}, cid {}, {}",
                cdb[cid].lit0(),
                lit,
                cid,
                &cdb[cid]
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
            cdb[cid]
                .iter()
                .skip(1)
                .map(|l| lit_level(asg, cdb, !*l, bag, mes))
                .max()
                .unwrap()
        }
        AssignReason::BinaryLink(b) => lit_level(asg, cdb, b, bag, mes),
        AssignReason::None => panic!("One of root of {} isn't assigned.", lit),
    }
}

#[allow(dead_code)]
fn dumper(asg: &AssignStack, cdb: &ClauseDB, bag: &[Lit]) -> String {
    let mut s = String::new();
    for l in bag {
        s.push_str(&format!(
            "{:8>} :: level {:4>}, {:?} {:?}\n",
            *l,
            asg.level(l.vi()),
            asg.reason(l.vi()),
            match asg.reason(l.vi()) {
                AssignReason::Decision(_) => vec![NULL_LIT],
                AssignReason::BinaryLink(lit) => vec![*l, !lit],
                AssignReason::Implication(cid) => cdb[cid].iter().copied().collect::<Vec<Lit>>(),
                AssignReason::None => vec![],
            },
        ));
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
        if let Ok(cid) = input.trim().parse::<usize>() {
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
                            .is(Flag::CA_SEEN)
                            .then(|| "S")
                            .unwrap_or(" "),
                        r
                    ))
                    .collect::<Vec<String>>()
                    .join("\n"),
            );
        }
    }
    panic!("done");
}

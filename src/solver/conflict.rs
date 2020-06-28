//! Conflict Analysis
use {
    super::{
        restart::{RestartIF, Restarter, RestarterModule},
        State,
    },
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarRewardIF},
        cdb::{ClauseDB, ClauseDBIF},
        processor::{EliminateIF, Eliminator},
        solver::SolverEvent,
        types::*,
    },
};

#[allow(clippy::cognitive_complexity)]
pub fn handle_conflict(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    ci: ClauseId,
) -> MaybeInconsistent {
    let original_dl = asg.decision_level();
    // we need a catch here for handling the possibility of level zero conflict
    // at higher level due to the incoherence between the current level and conflicting
    // level in chronoBT. This leads to UNSAT solution. No need to update misc stats.
    {
        let level = asg.level_ref();
        if cdb[ci].iter().all(|l| level[l.vi()] == 0) {
            return Err(SolverError::NullLearnt);
        }
    }

    let (num_conflict, _num_propagation, asg_num_restart, _) = asg.exports();
    // If we can settle this conflict w/o restart, solver will get a big progress.
    let switch_chronobt = if num_conflict < 1000 || asg.recurrent_conflicts() {
        Some(false)
    } else {
        None
    };
    rst.update(RestarterModule::Counter, num_conflict);

    if 0 < state.last_asg {
        rst.update(RestarterModule::ASG, asg.stack_len());
        state.last_asg = 0;
    }

    //
    //## DYNAMIC BLOCKING RESTART based on ASG, updated on conflict path
    //
    rst.block_restart();
    let mut use_chronobt = switch_chronobt.unwrap_or(0 < state.config.cbt_thr);
    if use_chronobt {
        let level = asg.level_ref();
        let c = &cdb[ci];
        let lit_count = c.iter().filter(|l| level[l.vi()] == original_dl).count();
        if 1 == lit_count {
            debug_assert!(c.iter().any(|l| level[l.vi()] == original_dl));
            let decision = *c.iter().find(|l| level[l.vi()] == original_dl).unwrap();
            let snd_l = c
                .iter()
                .map(|l| level[l.vi()])
                .filter(|l| *l != original_dl)
                .max()
                .unwrap_or(0);
            if 0 < snd_l {
                // If the conflicting clause contains one literal from the maximal
                // decision level, we let BCP propagating that literal at the second
                // highest decision level in conflicting cls.
                // PREMISE: 0 < snd_l
                asg.cancel_until(snd_l - 1);
                debug_assert!(
                    asg.stack_iter().all(|l| l.vi() != decision.vi()),
                    format!(
                        "assign stack contains a strange lit: level {}, stack level {}",
                        original_dl, snd_l
                    )
                );
                asg.assign_by_decision(decision);
                return Ok(());
            }
        }
    }
    // conflicting level
    // By mixing two restart modes, we must assume a conflicting level is under the current decision level,
    // even if `use_chronobt` is off, because `use_chronobt` is a flag for future behavior.
    let cl = {
        let cl = asg.decision_level();
        let c = &cdb[ci];
        let level = asg.level_ref();
        let lv = c.iter().map(|l| level[l.vi()]).max().unwrap_or(0);
        if lv < cl {
            asg.cancel_until(lv);
            lv
        } else {
            cl
        }
    };
    debug_assert!(
        cdb[ci].iter().any(|l| asg.level(l.vi()) == cl),
        format!(
            "use_{}: {:?}, {:?}",
            use_chronobt,
            cl,
            cdb[ci]
                .iter()
                .map(|l| (i32::from(*l), asg.level(l.vi())))
                .collect::<Vec<_>>(),
        )
    );
    // backtrack level by analyze
    let bl_a = conflict_analyze(asg, cdb, state, ci).max(asg.root_level);
    if state.new_learnt.is_empty() {
        #[cfg(debug)]
        {
            println!(
                "empty learnt at {}({}) by {:?}",
                cl,
                asg.reason(asg.decision_vi(cl)) == ClauseId::default(),
                asg.dump(asg, &cdb[ci]),
            );
        }
        return Err(SolverError::NullLearnt);
    }
    // asg.bump_vars(asg, cdb, ci);
    let new_learnt = &mut state.new_learnt;
    let l0 = new_learnt[0];
    // assert: 0 < cl, which was checked already by new_learnt.is_empty().

    // NCB places firstUIP on level bl, while CB does it on level cl.
    // Therefore the condition to use CB is: activity(firstUIP) < activity(v(bl)).
    // PREMISE: 0 < bl, because asg.decision_vi accepts only non-zero values.
    use_chronobt &= switch_chronobt.unwrap_or(
        bl_a == 0
            || state.config.cbt_thr + bl_a <= cl
            || asg.activity(l0.vi()) < asg.activity(asg.decision_vi(bl_a)),
    );

    // (assign level, backtrack level)
    let (al, bl) = if use_chronobt {
        (
            {
                let level = asg.level_ref();
                new_learnt[1..]
                    .iter()
                    .map(|l| level[l.vi()])
                    .max()
                    .unwrap_or(0)
            },
            cl - 1,
        )
    } else {
        (bl_a, bl_a)
    };
    let learnt_len = new_learnt.len();
    if learnt_len == 1 {
        //
        //## PARTIAL FIXED SOLUTION by UNIT LEARNT CLAUSE GENERATION
        //
        // dump to certified even if it's a literal.
        cdb.certificate_add(new_learnt);
        if use_chronobt {
            asg.cancel_until(bl);
            debug_assert!(asg.stack_iter().all(|l| l.vi() != l0.vi()));
            asg.assign_by_implication(l0, AssignReason::default(), 0);
        } else {
            asg.assign_by_unitclause(l0);
        }
        asg.handle(SolverEvent::Fixed);
        rst.update(RestarterModule::Reset, 0);
    } else {
        {
            // At the present time, some reason clauses can contain first UIP or its negation.
            // So we have to filter vars instead of literals to avoid double counting.
            let mut bumped = new_learnt.iter().map(|l| l.vi()).collect::<Vec<VarId>>();
            for lit in new_learnt.iter() {
                //
                //## Learnt Literal Rewarding
                //
                asg.reward_at_analysis(lit.vi());
                if !state.stabilize {
                    continue;
                }
                if let AssignReason::Implication(r, _) = asg.reason(lit.vi()) {
                    for l in &cdb[r].lits {
                        let vi = l.vi();
                        if !bumped.contains(&vi) {
                            //
                            //## Reason-Side Rewarding
                            //
                            asg.reward_at_analysis(vi);
                            bumped.push(vi);
                        }
                    }
                }
            }
        }
        asg.cancel_until(bl);
        let reason = if learnt_len == 2 {
            new_learnt[1]
        } else {
            NULL_LIT
        };
        let cid = cdb.new_clause(asg, new_learnt, true, true);
        elim.add_cid_occur(asg, cid, &mut cdb[cid], true);
        state.c_lvl.update(cl as f64);
        state.b_lvl.update(bl as f64);
        asg.assign_by_implication(l0, AssignReason::Implication(cid, reason), al);
        let lbd = cdb[cid].rank;
        rst.update(RestarterModule::LBD, lbd);
        if 1 < learnt_len && learnt_len <= state.config.elim_cls_lim / 2 {
            elim.to_simplify += 1.0 / (learnt_len - 1) as f64;
        }
    }
    cdb.scale_activity();
    if 0 < state.config.dump_int && num_conflict % state.config.dump_int == 0 {
        let (rst_num_block, rst_asg_trend, _lbd_get, rst_lbd_trend, _) = rst.exports();
        state.development.push((
            num_conflict,
            (asg.num_solved_vars + asg.num_eliminated_vars) as f64
                / state.target.num_of_variables as f64,
            asg_num_restart as f64,
            rst_num_block as f64,
            rst_asg_trend.min(10.0),
            rst_lbd_trend.min(10.0),
        ));
    }
    cdb.check_and_reduce(asg, num_conflict);
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
    conflicting_clause: ClauseId,
) -> DecisionLevel {
    let learnt = &mut state.new_learnt;
    learnt.clear();
    learnt.push(NULL_LIT);
    let dl = asg.decision_level();
    let mut p = cdb[conflicting_clause].lits[0];
    #[cfg(feature = "trace_analysis")]
    println!("- analyze conflicting literal {}", p);
    let mut path_cnt = 0;
    let vi = p.vi();
    if !asg.var(vi).is(Flag::CA_SEEN) && 0 < asg.level(vi) {
        let lvl = asg.level(vi);
        debug_assert!(!asg.var(vi).is(Flag::ELIMINATED));
        asg.var_mut(vi).turn_on(Flag::CA_SEEN);
        if dl <= lvl {
            path_cnt = 1;
            //
            //## Conflict-Side Rewarding
            //
            asg.reward_at_analysis(vi);
        } else {
            #[cfg(feature = "trace_analysis")]
            println!("- push {} to learnt, which level is {}", p, lvl);
            learnt.push(p);
        }
    }
    let mut reason = AssignReason::Implication(conflicting_clause, NULL_LIT);
    let mut ti = asg.stack_len() - 1; // trail index
    loop {
        match reason {
            AssignReason::Implication(_, l) if l != NULL_LIT => {
                // cid = asg.reason(p.vi());
                let vi = l.vi();
                if !asg.var(vi).is(Flag::CA_SEEN) {
                    let lvl = asg.level(vi);
                    if 0 == lvl {
                        continue;
                    }
                    debug_assert!(!asg.var(vi).is(Flag::ELIMINATED));
                    debug_assert!(asg.assign(vi).is_some());
                    asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                    if dl <= lvl {
                        path_cnt += 1;
                        asg.reward_at_analysis(vi);
                    } else {
                        #[cfg(feature = "boundary_check")]
                        panic!("strange level binary clause");
                    }
                }
            }
            AssignReason::Implication(cid, _) => {
                #[cfg(feature = "trace_analysis")]
                println!("analyze {}", p);
                debug_assert_ne!(cid, ClauseId::default());
                if cdb[cid].is(Flag::LEARNT) {
                    if !cdb[cid].is(Flag::JUST_USED) && !cdb.convert_to_permanent(asg, cid) {
                        cdb[cid].turn_on(Flag::JUST_USED);
                    }
                    cdb.bump_activity(cid, ());
                }
                let c = &cdb[cid];
                #[cfg(feature = "boundary_check")]
                assert!(
                    0 < c.len(),
                    format!(
                        "Level {} I-graph reaches {}:{} for {}:{}",
                        asg.decision_level(),
                        cid,
                        c,
                        p,
                        asg.var(p.vi())
                    )
                );
                #[cfg(feature = "trace_analysis")]
                println!("- handle {}", cid);
                for q in &c[1..] {
                    let vi = q.vi();
                    if !asg.var(vi).is(Flag::CA_SEEN) {
                        // asg.reward_at_analysis(vi);
                        let lvl = asg.level(vi);
                        if 0 == lvl {
                            continue;
                        }
                        debug_assert!(!asg.var(vi).is(Flag::ELIMINATED));
                        debug_assert!(asg.assign(vi).is_some());
                        asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                        if dl <= lvl {
                            // println!("- flag for {} which level is {}", q.int(), lvl);
                            path_cnt += 1;
                            //
                            //## Conflict-Side Rewarding
                            //
                            asg.reward_at_analysis(vi);
                        } else {
                            #[cfg(feature = "trace_analysis")]
                            println!("- push {} to learnt, which level is {}", q, lvl);
                            learnt.push(*q);
                        }
                    } else {
                        #[cfg(feature = "trace_analysis")]
                        {
                            if !asg.var(vi).is(Flag::CA_SEEN) {
                                println!("- ignore {} because it was flagged", q);
                            } else {
                                println!("- ignore {} because its level is {}", q, asg.level(vi));
                            }
                        }
                    }
                }
            }
            AssignReason::None => {
                #[cfg(feature = "boundary_check")]
                panic!("conflict_analyze: faced AssignReason::None.");
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
            assert!(
                vi < asg.level_ref().len(),
                format!("ti:{}, lit:{}, len:{}", ti, asg.stack(ti), asg.stack_len())
            );
            let lvl = asg.level(vi);
            let v = asg.var(vi);
            !v.is(Flag::CA_SEEN) || lvl != dl
        } {
            #[cfg(feature = "trace_analysis")]
            println!("- skip {} because it isn't flagged", asg.stack(ti));
            #[cfg(feature = "boundary_check")]
            assert!(
                0 < ti,
                format!(
                    "p:{}, path_cnt:{}, lv:{}, learnt:{:?}\nconflict:{:?}",
                    p,
                    path_cnt,
                    dl,
                    asg.dump(&*learnt),
                    asg.dump(&cdb[conflicting_clause].lits),
                ),
            );
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

#[allow(clippy::cognitive_complexity)]
pub fn conflict_analyze_sandbox(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    conflicting_clause: ClauseId,
) -> DecisionLevel {
    let learnt = &mut state.new_learnt;
    learnt.clear();
    learnt.push(NULL_LIT);
    let dl = asg.decision_level();
    let mut p = cdb[conflicting_clause].lits[0];
    let mut path_cnt = 0;
    let vi = p.vi();
    if !asg.var(vi).is(Flag::CA_SEEN) && 0 < asg.level(vi) {
        let lvl = asg.level(vi);
        asg.var_mut(vi).turn_on(Flag::CA_SEEN);
        if dl <= lvl {
            path_cnt = 1;
        } else {
            learnt.push(p);
        }
    }
    let mut reason = AssignReason::Implication(conflicting_clause, NULL_LIT);
    let mut ti = asg.stack_len() - 1;
    loop {
        match reason {
            AssignReason::Implication(_, l) if l != NULL_LIT => {
                let vi = l.vi();
                if !asg.var(vi).is(Flag::CA_SEEN) {
                    let lvl = asg.level(vi);
                    if 0 == lvl {
                        continue;
                    }
                    asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                    if dl <= lvl {
                        path_cnt += 1;
                    }
                }
            }
            AssignReason::Implication(cid, _) => {
                if cdb[cid].is(Flag::LEARNT)
                    && !cdb[cid].is(Flag::JUST_USED)
                    && !cdb.convert_to_permanent(asg, cid)
                {
                    cdb[cid].turn_on(Flag::JUST_USED);
                }
                let c = &cdb[cid];
                for q in &c[1..] {
                    let vi = q.vi();
                    if !asg.var(vi).is(Flag::CA_SEEN) {
                        let lvl = asg.level(vi);
                        if 0 == lvl {
                            continue;
                        }
                        asg.var_mut(vi).turn_on(Flag::CA_SEEN);
                        if dl <= lvl {
                            path_cnt += 1;
                        } else {
                            learnt.push(*q);
                        }
                    }
                }
            }
            AssignReason::None => (),
        }
        while {
            let vi = asg.stack(ti).vi();
            let lvl = asg.level(vi);
            let v = asg.var(vi);
            !v.is(Flag::CA_SEEN) || lvl != dl
        } {
            ti -= 1;
        }
        p = asg.stack(ti);
        asg.var_mut(p.vi()).turn_off(Flag::CA_SEEN);
        path_cnt -= 1;
        if path_cnt == 0 {
            break;
        }
        ti -= 1;
        reason = asg.reason(p.vi());
    }
    learnt[0] = !p;
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
        assert!(!new_learnt.is_empty());
        new_learnt.retain(|l| *l == l0 || !l.is_redundant(asg, cdb, &mut to_clear, &levels));
        let len = new_learnt.len();
        if 2 < len && len < 30 {
            cdb.minimize_with_biclauses(asg, new_learnt);
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
/// any leaf of implication graph for it isn't a fixed var nor a decision var.
impl Lit {
    fn is_redundant(
        self,
        asg: &mut AssignStack,
        cdb: &ClauseDB,
        clear: &mut Vec<Lit>,
        levels: &[bool],
    ) -> bool {
        if asg.reason(self.vi()) == AssignReason::default() {
            return false;
        }
        let mut stack = Vec::new();
        stack.push(self);
        let top = clear.len();
        while let Some(sl) = stack.pop() {
            match asg.reason(sl.vi()) {
                AssignReason::None => panic!("no idea"),
                AssignReason::Implication(_, l) if l != NULL_LIT => {
                    let vi = l.vi();
                    let lv = asg.level(vi);
                    if 0 < lv && !asg.var(vi).is(Flag::CA_SEEN) {
                        if asg.reason(vi) != AssignReason::default() && levels[lv as usize] {
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
                AssignReason::Implication(cid, _) => {
                    let c = &cdb[cid];
                    #[cfg(feature = "boundary_check")]
                    assert!(0 < c.len());
                    for q in &(*c)[1..] {
                        let vi = q.vi();
                        let lv = asg.level(vi);
                        if 0 < lv && !asg.var(vi).is(Flag::CA_SEEN) {
                            if asg.reason(vi) != AssignReason::default() && levels[lv as usize] {
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
            }
        }
        true
    }
}

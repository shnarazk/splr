/// Conflict Analysis
use crate::{
    assign::{AssignIF, AssignStack, VarManipulateIF, VarRewardIF},
    cdb::{ClauseDB, ClauseDBIF},
    state::State,
    types::*,
};

///
/// ## Conflict Analysis
///
#[allow(clippy::cognitive_complexity)]
pub fn conflict_analyze(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    state: &mut State,
    confl: ClauseId,
) -> DecisionLevel {
    let learnt = &mut state.new_learnt;
    learnt.clear();
    learnt.push(NULL_LIT);
    let dl = asg.decision_level();
    let mut p = NULL_LIT;
    let mut ti = asg.stack_len() - 1; // trail index
    let mut path_cnt = 0;
    loop {
        let reason = if p == NULL_LIT {
            AssignReason::Implication(confl, NULL_LIT)
        } else {
            asg.reason(p.vi())
        };
        match reason {
            AssignReason::None => panic!("here"),
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
                        #[cfg(feature = "trace_analysis")]
                        println!("- push {} to learnt, which level is {}", q.int(), lvl);
                        // learnt.push(l);
                    }
                } else {
                    #[cfg(feature = "trace_analysis")]
                    {
                        if !asg.var(vi).is(Flag::CA_SEEN) {
                            println!("- ignore {} because it was flagged", q.int());
                        } else {
                            println!("- ignore {} because its level is {}", q.int(), lvl);
                        }
                    }
                }
            }
            AssignReason::Implication(cid, _) => {
                #[cfg(feature = "trace_analysis")]
                println!("analyze {}", p.int());
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
                println!("- handle {}", cid.fmt());
                for q in &c[(p != NULL_LIT) as usize..] {
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
                            println!("- push {} to learnt, which level is {}", q.int(), lvl);
                            learnt.push(*q);
                        }
                    } else {
                        #[cfg(feature = "trace_analysis")]
                        {
                            if !asg.var(vi).is(Flag::CA_SEEN) {
                                println!("- ignore {} because it was flagged", q.int());
                            } else {
                                println!("- ignore {} because its level is {}", q.int(), lvl);
                            }
                        }
                    }
                }
            }
        }
        // The following case was subsumed into `search`.
        /*
        // In an unsat problem, a conflict can occur at decision level zero
        // by a clause which literals' levels are zero.
        // So we have the posibility getting the following situation.
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
            println!("- skip {} because it isn't flagged", asg[ti].int());
            #[cfg(feature = "boundary_check")]
            assert!(
                0 < ti,
                format!(
                    "p:{}, path_cnt:{}, lv:{}, learnt:{:?}\nconflict:{:?}",
                    p,
                    path_cnt,
                    dl,
                    asg.dump(&*learnt),
                    asg.dump(&cdb[confl].lits),
                ),
            );
            ti -= 1;
        }
        p = asg.stack(ti);
        #[cfg(feature = "trace_analysis")]
        println!(
            "- move to flagged {}, which reason is {}; num path: {}",
            p.vi(),
            path_cnt - 1,
            cid.fmt()
        );
        asg.var_mut(p.vi()).turn_off(Flag::CA_SEEN);
        // since the trail can contain a literal which level is under `dl` after
        // the `dl`-th thdecision var, we must skip it.
        path_cnt -= 1;
        if path_cnt == 0 {
            break;
        }
        debug_assert!(0 < ti);
        ti -= 1;
    }
    debug_assert!(learnt.iter().all(|l| *l != !p));
    debug_assert_eq!(asg.level(p.vi()), dl);
    learnt[0] = !p;
    #[cfg(feature = "trace_analysis")]
    println!(
        "- appending {}, the result is {:?}",
        learnt[0].int(),
        vec2int(learnt)
    );
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

pub fn analyze_final(asg: &mut AssignStack, state: &mut State, c: &Clause) {
    let mut seen = vec![false; asg.num_vars + 1];
    state.conflicts.clear();
    if asg.decision_level() == 0 {
        return;
    }
    for l in &c.lits {
        let vi = l.vi();
        if 0 < asg.level(vi) {
            asg.var_mut(vi).turn_on(Flag::CA_SEEN);
        }
    }
    let end = if asg.decision_level() <= asg.root_level {
        asg.stack_len()
    } else {
        asg.len_upto(asg.root_level)
    };
    for l in asg.stack_range(asg.len_upto(0)..end) {
        let vi = l.vi();
        if seen[vi] {
            if asg.reason(vi) == AssignReason::default() {
                state.conflicts.push(!*l);
            } else {
                let level = asg.level_ref();
                for l in &c[(c.len() != 2) as usize..] {
                    let vj = l.vi();
                    if 0 < level[vj] {
                        seen[vj] = true;
                    }
                }
            }
        }
        seen[vi] = false;
    }
}

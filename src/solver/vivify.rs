//! Vivification
#![allow(dead_code)]
#![cfg(feature = "clause_vivification")]
use {
    super::{Restarter, Stat, State},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{self, ClauseDB, ClauseDBIF, ClauseIF},
        processor::{EliminateIF, Eliminator},
        state::StateIF,
        types::*,
    },
};

#[derive(Clone, Debug, Eq, PartialEq)]
enum VivifyResult {
    Conflict(Vec<Lit>),
    NoConflict,
    Satisifed,
}

/// vivify clauses in `cdb` under `asg`
#[cfg(not(feature = "clause_vivification"))]
pub fn vivify(
    _asg: &mut AssignStack,
    _cdb: &mut ClauseDB,
    _elim: &mut Eliminator,
    _state: &mut State,
) -> MaybeInconsistent {
    Ok(())
}

pub fn vivify(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    average_lbd: f64,
) -> MaybeInconsistent {
    assert_eq!(asg.root_level, asg.decision_level());
    if elim.simplify(asg, cdb, rst, state).is_err() {
        panic!("eaeuae");
    }
    let mut clauses: Vec<OrderedProxy<ClauseId>> = Vec::new();
    {
        let thr = (average_lbd + cdb.derefer(cdb::property::Tf64::DpAverageLBD)) as usize;
        for (i, c) in cdb.iter().enumerate().skip(1) {
            if let Some(act) = c.to_vivify(thr) {
                clauses.push(OrderedProxy::new(ClauseId::from(i), -act));
            }
        }
    }
    if clauses.is_empty() {
        return Ok(());
    }
    clauses.sort();
    let num_target = clauses.len();
    state[Stat::Vivification] += 1;
    let dl = asg.decision_level();
    debug_assert_eq!(dl, 0);
    // This is a reusable vector to reduce memory consumption,
    // the key is the number of invocation
    let mut seen: Vec<usize> = vec![0; asg.num_vars + 1];
    let display_step: usize = 1000;
    let mut num_check = 0;
    let mut num_purge = 0;
    let mut num_shrink = 0;
    let mut num_assert = 0;
    let mut to_display = 0;
    // let activity_thr = cdb.derefer(cdb::property::Tf64::DpAverageLBD);

    while let Some(cs) = clauses.pop() {
        let cid = cs.to();
        if cdb[cid].is_dead() {
            continue;
        }
        if cdb[cid].is_satisfied_under(asg) {
            // cdb.remove_clause(cid);
            continue;
        }
        if cdb[cid].to_vivify(0).is_none() {
            continue;
        }
        assert!(cdb[cid].to_vivify(10).is_some());
        // assert_eq!(asg.root_level, asg.decision_level());
        let activity = cdb.activity(cid);
        let is_learnt = cdb[cid].is(Flag::LEARNT);
        let c: &mut Clause = &mut cdb[cid];
        debug_assert!(!c.is(Flag::ELIMINATED));
        c.vivified();
        let clits = c.iter().map(|l| *l).collect::<Vec<Lit>>();
        let mut decisions: Vec<Lit> = Vec::new();
        if to_display <= num_check {
            state.flush("");
            if num_target < 2 * num_purge {
                state.flush(format!(
                    "clause vivifying was canceled due to too high purge rate {:>5.3}. ",
                    num_purge as f64 / num_check as f64,
                ));
                return Ok(());
            }
            state.flush(format!(
                "clause vivifying(assert:{}, purge:{} shorten:{}, check:{}/{})...",
                num_assert, num_purge, num_shrink, num_check, num_target,
            ));
            to_display = num_check + display_step;
        }
        num_check += 1;
        seen[0] = num_check;
        debug_assert_eq!(asg.root_level, asg.decision_level());
        debug_assert!(clits.iter().all(|l| !clits.contains(&!*l)));
        let mut result = VivifyResult::NoConflict;
        'this_clause: for l in clits.iter().map(|ol| *ol) {
            debug_assert!(!asg.var(l.vi()).is(Flag::ELIMINATED));
            match asg.assigned(l) {
                //
                //## Rule 1
                //
                Some(false) => continue 'this_clause,
                //
                //## Rule 2
                //
                Some(true) => {
                    panic!("why");
                    result = VivifyResult::Satisifed;
                    break 'this_clause;
                }
                None => {
                    let cid: Option<ClauseId> = match decisions.len() {
                        0 => None,
                        1 => {
                            asg.assign_by_decision(decisions[0]);
                            None
                        }
                        _ => cdb.new_clause_sandbox(asg, &mut decisions.clone()).is_new(),
                    };
                    decisions.push(!l);
                    asg.assign_by_decision(!l);
                    //
                    //## Rule 3
                    //
                    if let Some(cc) = asg.propagate_sandbox(cdb).to_option() {
                        // / let mut ccl = cdb[cc].iter().map(|l| *l).collect::<Vec<_>>();
                        // / ccl.sort();
                        // / let mut sorted = clits.clone();
                        // / sorted.sort();
                        // / let ccl1 = ccl.iter().filter(|l| 0 < asg.level(l.vi())).collect::<Vec<_>>();
                        // / let sorted1 = sorted.iter().filter(|l| 0 < asg.level(l.vi())).collect::<Vec<_>>();
                        // / assert_eq!(ccl, sorted,
                        // /            "{:?}({:?}) != {:?}({:?})",
                        // /            ccl,
                        // /            ccl1,
                        // /            sorted,
                        // /            sorted1,
                        // / );
                        // /
                        // / assert!(!cdb[cc].is_empty());
                        // / if cid.map_or(false, |ci| ci != cc) {
                        // /     asg.backtrack_sandbox();
                        // /     cid.map(|cj| cdb.remove_clause_sandbox(cj));
                        // /     continue 'next_clause;
                        // / }
                        // There's a posibility for a satisfied clause to come here.
                        // This maybe be the reason of broken UNSAT certificates.
                        debug_assert!(!cdb[cc].is_empty());
                        debug_assert!(0 < decisions.len());
                        let learnt = asg.analyze_sandbox(
                            cdb,
                            &decisions, // decision literals
                            &cdb[cc].iter().map(|l| *l).collect::<Vec<Lit>>(),
                            &mut seen,
                        );
                        asg.backtrack_sandbox();
                        cid.map(|cj| cdb.remove_clause_sandbox(cj));
                        debug_assert!(!learnt.is_empty());
                        result = VivifyResult::Conflict(learnt);
                        break 'this_clause;
                    }
                    //
                    //## Rule 4
                    //
                    asg.backtrack_sandbox();
                    cid.map(|cj| cdb.remove_clause_sandbox(cj));
                }
            }
        }
        match result {
            VivifyResult::Satisifed => {
                cdb.remove_clause(cid);
                num_purge += 1;
            }
            VivifyResult::NoConflict => {
                let new_len = decisions.len();
                debug_assert!(1 < new_len);
                if new_len < clits.len() {
                    flip(&mut decisions);
                    if let Some(ci) = cdb.new_clause(asg, &mut decisions, is_learnt).is_new() {
                        cdb.set_activity(ci, activity);
                        cdb[ci].turn_on(Flag::VIVIFIED);
                    }
                    elim.to_simplify += 1.0 / new_len as f64;
                    num_shrink += 1;
                    cdb.remove_clause(cid);
                }
            }
            VivifyResult::Conflict(mut learnt) => {
                let new_len = learnt.len();
                debug_assert!(0 < new_len);
                if new_len == 1 {
                    assert_eq!(asg.root_level, asg.decision_level());
                    let l0 = learnt[0];
                    match asg.assigned(l0) {
                        None => {
                            cdb.certificate_add_assertion(l0);
                            if asg.assign_at_root_level(l0).is_err() {
                                panic!("vviy181");
                                // return Err(SolverError::Inconsistent);
                            }
                            num_assert += 1;
                            state[Stat::VivifiedVar] += 1;
                        }
                        Some(false) => panic!("vivify176"),
                        _ => (),
                    }
                    debug_assert!(clits.contains(&l0));
                    cdb.remove_clause(cid);
                    num_purge += 1;
                    if let Some(cc) = asg.propagate(cdb).to_option() {
                        panic!("vivify193 found an inconsisteny: target:{}, cc:{}", cid, cc);
                        // return Err(SolverError::Inconsistent);
                    }
                    if elim.simplify(asg, cdb, rst, state).is_err() {
                        panic!("eaeuae");
                    }
                } else {
                    let related = learnt.iter().all(|l| clits.contains(l));
                    assert!(
                        learnt.iter().all(|l| clits.contains(l)),
                        "{:?} < {:?}",
                        clits,
                        learnt,
                    );
                    if let Some(ci) = cdb.new_clause(asg, &mut learnt, is_learnt).is_new() {
                        cdb.set_activity(ci, activity);
                        cdb[ci].turn_on(Flag::VIVIFIED);
                    }
                    elim.to_simplify += 1.0 / new_len as f64;
                    assert!(related);
                    if related {
                        cdb.remove_clause(cid);
                        num_shrink += 1;
                    }
                }
                clauses.retain(|cs| {
                    !cdb[cs.to()].is_dead()
                        && !cdb[cid].is_satisfied_under(asg)
                        && cdb[cid].to_vivify(0).is_some()
                });
            }
        }
    }
    state.log(
        state[Stat::Vivification],
        format!(
            "vivify, pick:{:>8}, var:{:>6}, purge:{:>6}, shrink:{:>6}",
            num_check, num_assert, num_purge, num_shrink,
        ),
    );
    state[Stat::VivifiedClause] += num_shrink + num_purge;
    state[Stat::VivifiedVar] += num_assert;
    Ok(())
}

fn flip(vec: &mut [Lit]) -> &mut [Lit] {
    for l in vec.iter_mut() {
        *l = !*l;
    }
    vec
}

impl AssignStack {
    /// inspect the complete implication graph to collect a disjunction of a subset of
    /// negated literals of `lits`
    fn analyze_sandbox(
        &self,
        cdb: &ClauseDB,
        decisions: &[Lit],
        conflicting: &[Lit],
        seen: &mut [usize],
    ) -> Vec<Lit> {
        let key = seen[0];
        let mut learnt: Vec<Lit> = Vec::new();
        for l in conflicting {
            seen[l.vi()] = key;
        }
        let last_decision = decisions.last().unwrap();
        let from = self.len_upto(self.root_level);
        let all = self.stack_iter().skip(0).map(|l| !*l).collect::<Vec<_>>();
        let assumes = &all[from..];
        debug_assert!(
            all.iter().all(|l| !assumes.contains(&!*l)),
            "vivify252\n{:?}, {:?}",
            assumes
                .iter()
                .filter(|l| all.contains(&!**l))
                .collect::<Vec<_>>(),
            assumes
                .iter()
                .filter(|l| all.contains(&!**l))
                .map(|l| self.reason(l.vi()))
                .collect::<Vec<_>>(),
            // am.iter().filter(|l| am.contains(&!**l)).collect::<Vec<_>>(),
        );
        // sweep in the reverse order
        for l in self.stack_iter().skip(self.len_upto(0)).rev() {
            if seen[l.vi()] != key
            /* || l == last_decision */
            {
                continue;
            }
            if decisions.contains(l) {
                assert!(!learnt.contains(l));
                // Quiz: which is the correct learnt clause here?
                // 1. [decision1, decision2, !last_decision]
                // 2. [!decision1, !decision2, !last_decision]
                // Since `conflict::conflict_analyze` sweeps *reason caluses*,
                // it collects positive literals in a list. while we collect decision
                // literals in *trail* here. Thus we must negate the literals.
                learnt.push(!*l);
            }
            match self.reason(l.vi()) {
                AssignReason::Implication(_, bil) if bil != NULL_LIT => {
                    seen[bil.vi()] = key;
                }
                AssignReason::Implication(cid, _) => {
                    for r in cdb[cid].iter().skip(1) {
                        seen[r.vi()] = key;
                    }
                }
                _ => (),
            }
        }
        // make sure the decision var is at the top of list
        // if res.is_empty() {
        //     return
        // }
        debug_assert!(
            !learnt.is_empty(),
            "empty learnt, conflict: {:?}, assumed: {:?}",
            conflicting,
            decisions
        );
        debug_assert!(
            learnt.contains(&!*last_decision),
            "\nThe negation of the last decision {} isn't contained in {:?}",
            last_decision,
            learnt,
        );
        // Since we don't assign the right value of the 'reason' literal after conflict analysis,
        // we need not to swap locations.
        // learnt.swap(0, lst);
        // assert!(matches!(self.reason(learnt[0].vi()), AssignReason::None));
        debug_assert!(
            learnt.iter().all(|l| !learnt.contains(&!*l)),
            "res: {:?} from: {:?} and trail: {:?}",
            learnt,
            decisions,
            assumes,
        );
        learnt
    }
}

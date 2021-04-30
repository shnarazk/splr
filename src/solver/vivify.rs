//! Vivification
#![allow(dead_code)]
#![cfg(feature = "clause_vivification")]
use {
    super::{Stat, State},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{self, ClauseDB, ClauseDBIF, ClauseIF},
        processor::Eliminator,
        state::StateIF,
        types::*,
    },
};

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
    state: &mut State,
    average_lbd: f64,
) -> MaybeInconsistent {
    assert_eq!(asg.root_level, asg.decision_level());
    let mut clauses: Vec<OrderedProxy<ClauseId>> = Vec::new();
    {
        let thr = (average_lbd + cdb.derefer(cdb::property::Tf64::DpAverageLBD)) as usize;
        for (i, c) in cdb.iter().enumerate().skip(1) {
            if c.is(Flag::LEARNT) {
                if let Some(act) = c.to_vivify(thr) {
                    clauses.push(OrderedProxy::new(ClauseId::from(i), -act));
                }
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

    'next_clause: while let Some(cs) = clauses.pop() {
        let cid = cs.to();
        if cdb[cid].is_dead() {
            continue;
        }
        if cdb[cid].is_satisfied_under(asg) {
            // cdb.remove_clause(cid);
            continue;
        }
        // assert_eq!(asg.root_level, asg.decision_level());
        let activity = cdb.activity(cid);
        let is_learnt = cdb[cid].is(Flag::LEARNT);
        let c: &mut Clause = &mut cdb[cid];
        debug_assert!(!c.is(Flag::ELIMINATED));
        c.vivified();
        let clits = c.iter().map(|l| *l).collect::<Vec<Lit>>();
        let mut copied: Vec<Lit> = Vec::new();
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
        assert_eq!(asg.root_level, asg.decision_level());
        assert!(clits.iter().all(|l| !clits.contains(&!*l)));
        enum VivifyResult {
            Conflict(Vec<Lit>),
            NoConflict,
            Satisifed,
        }
        let mut result = VivifyResult::NoConflict;
        'this_clause: for l in clits.iter().map(|ol| *ol) {
            assert!(!asg.var(l.vi()).is(Flag::ELIMINATED));
            match asg.assigned(l) {
                //
                //## Rule 1
                //
                Some(false) => continue 'this_clause,
                //
                //## Rule 2
                //
                Some(true) => {
                    result = VivifyResult::Satisifed;
                    break 'this_clause;
                }
                // None if 2 < copied.len() && false => {
                //     // avoid clause duplication
                //     continue 'next_clause;
                // }
                None => {
                    let cid: Option<ClauseId> = match copied.len() {
                        0 => None,
                        1 => {
                            // assert_eq!(asg.assigned(copied[0]), None);
                            asg.assign_by_decision(copied[0]);
                            None
                        }
                        _ => cdb.new_clause_sandbox(asg, &mut copied.clone()).is_new(),
                    };
                    copied.push(!l);
                    // assert_eq!(asg.assigned(!l), None);
                    asg.assign_by_decision(!l);
                    //
                    //## Rule 3
                    //
                    if let Some(cc) = asg.propagate_sandbox(cdb).to_option() {
                        assert!(!cdb[cc].is_empty());
                        if cid.map_or(false, |ci| ci != cc) {
                            asg.backtrack_sandbox();
                            cid.map(|cj| cdb.remove_clause_sandbox(cj));
                            continue 'next_clause;
                        }
                        // There's a posibility for a satisfied clause to come here.
                        // This maybe be the reason of broken UNSAT certificates.
                        assert!(!cdb[cc].is_empty());
                        assert!(0 < copied.len());
                        let learnt = asg.analyze_sandbox(
                            cdb,
                            &copied,
                            &cdb[cc].iter().map(|l| *l).collect::<Vec<Lit>>(),
                            &mut seen,
                        );
                        asg.backtrack_sandbox();
                        cid.map(|cj| cdb.remove_clause_sandbox(cj));
                        assert!(!learnt.is_empty());
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
                let new_len = copied.len();
                assert!(1 < new_len);
                if new_len < clits.len() {
                    flip(&mut copied);
                    if let Some(ci) = cdb.new_clause(asg, &mut copied, true).is_new() {
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
                assert!(0 < new_len);
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
                    cdb.remove_clause(cid);
                    num_purge += 1;
                    if let Some(cc) = asg.propagate(cdb).to_option() {
                        panic!("vivify193 found an inconsisteny: target:{}, cc:{}", cid, cc);
                        // return Err(SolverError::Inconsistent);
                    }
                    clauses.retain(|cs| !cdb[cs.to()].is_dead());
                } else {
                    if let Some(ci) = cdb.new_clause(asg, &mut learnt, true).is_new() {
                        cdb.set_activity(ci, activity);
                        cdb[ci].turn_on(Flag::VIVIFIED);
                    }
                    elim.to_simplify += 1.0 / new_len as f64;
                    num_shrink += 1;
                    cdb.remove_clause(cid);
                }
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
        assumed_lits: &[Lit],
        conflicting: &[Lit],
        seen: &mut [usize],
    ) -> Vec<Lit> {
        let key = seen[0];
        let mut res: Vec<Lit> = Vec::new();
        for l in conflicting {
            seen[l.vi()] = key;
        }
        let from = self.len_upto(self.root_level);
        let all = self.stack_iter().skip(0).map(|l| !*l).collect::<Vec<_>>();
        let assumes = &all[from..];
        assert!(
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
            if seen[l.vi()] != key {
                continue;
            }
            if assumed_lits.contains(l) || true {
                assert!(!res.contains(l));
                res.push(!*l);
                // } else {
                //     panic!("eaeae");
            }
            if let AssignReason::Implication(cid, _) = self.reason(l.vi()) {
                for r in cdb[cid].iter() {
                    seen[r.vi()] = key;
                }
            }
        }
        // make sure the decision var is at the top of list
        // if res.is_empty() {
        //     return
        // }
        assert!(
            !res.is_empty(),
            "empty learnt, conflict: {:?}, assumed: {:?}",
            conflicting,
            assumed_lits
        );
        let lst = res.len() - 1;
        res.swap(0, lst);
        assert!(matches!(self.reason(res[0].vi()), AssignReason::None));
        assert!(
            res.iter().all(|l| !res.contains(&!*l)),
            "res: {:?} from: {:?} and trail: {:?}",
            res,
            assumed_lits,
            assumes,
        );
        res
    }
}

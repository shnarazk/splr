//! Vivification
#![allow(dead_code)]
#![cfg(feature = "clause_vivification")]
use {
    super::{Stat, State},
    crate::{
        assign::{self, AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{self, ClauseDB, ClauseDBIF, ClauseIF, CID},
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
) -> MaybeInconsistent {
    assert_eq!(asg.root_level, asg.decision_level());
    let mut clauses: Vec<OrderedProxy<ClauseId>> = Vec::new();
    {
        let thr = 10
            + 26usize.saturating_sub(
                ((asg.derefer(assign::property::Tusize::NumUnassertedVar) as f64).log2()
                    + (cdb.derefer(cdb::property::Tusize::NumClause) as f64).log10())
                    as usize,
            );
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

    while let Some(cs) = clauses.pop() {
        assert_eq!(asg.root_level, asg.decision_level());
        let activity = cdb.activity(cs.to());
        let is_learnt = cdb[cs.to()].is(Flag::LEARNT);
        let c: &mut Clause = &mut cdb[cs.to()];
        if c.is_dead() {
            continue;
        }
        debug_assert!(!c.is(Flag::ELIMINATED));
        c.vivified();
        let clits = c.iter().map(|l| *l).collect::<Vec<Lit>>();
        let mut copied: Vec<Lit> = Vec::new();
        let mut flipped = true;
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
        assert_eq!(asg.root_level, asg.decision_level());
        'this_clause: for l in clits.iter().map(|ol| *ol) {
            seen[0] = num_check;
            match asg.assigned(l) {
                //
                //## Rule 1
                //
                Some(false) => continue 'this_clause,
                //
                //## Rule 2
                //
                Some(true) => {
                    copied.clear();
                    flipped = false;
                    break 'this_clause;
                }
                None => {
                    let cid: Option<ClauseId> = match copied.len() {
                        0 => None,
                        1 => {
                            asg.assign_by_decision(copied[0]);
                            None
                        }
                        _ => {
                            if let CID::Generated(cid) =
                                cdb.new_clause_sandbox(asg, &mut copied.clone())
                            {
                                Some(cid)
                            } else {
                                None
                            }
                        }
                    };
                    asg.assign_by_decision(!l);
                    let cc: ClauseId = asg.propagate_sandbox(cdb);
                    //
                    //## Rule 3
                    //
                    if !cc.is_none() {
                        copied.push(!l);
                        copied = asg.analyze(
                            cdb,
                            &copied,
                            &cdb[cc].iter().map(|l| *l).collect::<Vec<Lit>>(),
                            &mut seen,
                        );
                        if copied.is_empty() {
                            break 'this_clause;
                        }
                        flipped = false;
                    }
                    asg.backtrack_sandbox();
                    cid.map(|cj| cdb.remove_clause_sandbox(cj));
                    //
                    //## Rule 4
                    //
                    copied.push(!l);
                }
            }
        }
        debug_assert!(!cdb[cs.to()].is_dead());
        if flipped {
            flip(&mut copied);
        }
        match copied.len() {
            0 if flipped => {
                cdb.certificate_add_assertion(clits[0]);
                return Err(SolverError::Inconsistent);
            }
            // 0 if average_timestamp < timestamp => (),
            0 => {
                cdb.remove_clause(cs.to());
                num_purge += 1;
            }
            1 => {
                assert_eq!(asg.decision_level(), asg.root_level);
                let l0 = copied[0];
                match asg.assigned(l0) {
                    None => {
                        cdb.certificate_add_assertion(l0);
                        if asg.assign_at_root_level(l0).is_err() {
                            return Err(SolverError::Inconsistent);
                        }
                        num_assert += 1;
                        state[Stat::VivifiedVar] += 1;
                    }
                    Some(false) => panic!("vivify176"),
                    _ => (),
                }
                cdb.remove_clause(cs.to());
                if !asg.propagate_sandbox(cdb).is_none() {
                    // panic!("Vivification found an inconsistency.");
                    return Err(SolverError::Inconsistent);
                }
                num_purge += 1;
            }
            n if n == clits.len() => (),
            n => {
                match cdb.new_clause(asg, &mut copied, is_learnt, true) {
                    CID::Generated(ci) => {
                        cdb.set_activity(ci, activity);
                        cdb[ci].turn_on(Flag::VIVIFIED);
                        elim.to_simplify += 1.0 / (n as f64).powf(1.4);
                    }
                    CID::Merged(ci) => {
                        cdb[ci].turn_on(Flag::VIVIFIED);
                        elim.to_simplify += 0.5;
                    }
                }
                cdb.remove_clause(cs.to());
                num_shrink += 1;
            }
        }
        assert_eq!(asg.root_level, asg.decision_level());
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
    fn analyze(
        &self,
        cdb: &ClauseDB,
        lits: &[Lit],
        reason: &[Lit],
        seen: &mut [usize],
    ) -> Vec<Lit> {
        let key = seen[0];
        let mut res: Vec<Lit> = Vec::new();
        for l in reason {
            seen[l.vi()] = key;
        }
        // make sure the decision var is at the top of list
        if let Some(l) = lits.last().filter(|l| reason.contains(l)) {
            res.push(*l);
            seen[l.vi()] = 0;
        }
        // sweep
        for l in self.stack_iter().skip(self.len_upto(0)).rev() {
            if seen[l.vi()] != key {
                continue;
            }
            if lits.contains(l) {
                assert!(res.iter().all(|lit| lit.vi() != l.vi()));
                res.push(!*l);
            } else if lits.contains(&!*l) {
                assert!(res.iter().all(|lit| lit.vi() != l.vi()));
                res.push(*l);
            }

            match self.reason(l.vi()) {
                AssignReason::Implication(cid, _) => {
                    for r in cdb[cid].iter() {
                        seen[r.vi()] = key;
                    }
                }
                AssignReason::None => {
                    seen[l.vi()] = key;
                }
            }
        }
        res
    }
}

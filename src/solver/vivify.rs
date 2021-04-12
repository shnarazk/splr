//! Vivification
#![allow(dead_code)]
#![cfg(feature = "clause_vivification")]
use {
    super::{Stat, State},
    crate::{
        assign::{self, AssignIF, AssignStack, PropagateIF, VarManipulateIF},
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
) -> MaybeInconsistent {
    let mut average_age: f64 = 0.0;
    let mut clauses: Vec<OrderedProxy<ClauseId>> = Vec::new();
    {
        let thr = 8 + 20usize.saturating_sub(
            ((asg.derefer(assign::property::Tusize::NumUnassertedVar) as f64).log2()
                + (cdb.derefer(cdb::property::Tusize::NumClause) as f64).log10())
                as usize,
        );
        for (i, c) in cdb.iter().enumerate().skip(1) {
            if c.is(Flag::LEARNT) {
                if let Some(act) = c.to_vivify(thr) {
                    average_age += c.timestamp() as f64;
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
    // This is a reusable vector to reduce memory consumption, the key is the number of invocation
    let mut seen: Vec<usize> = vec![0; asg.num_vars + 1];
    let display_step: usize = 100;
    let mut num_check = 0;
    let mut num_purge = 0;
    let mut num_shrink = 0;
    let mut num_assert = 0;
    let mut to_display = 0;
    let average_timestamp = average_age as usize / num_target;
    let _activity_thr = cdb.derefer(cdb::property::Tf64::DpAverageLBD);

    while let Some(cs) = clauses.pop() {
        let c: &mut Clause = &mut cdb[cs.to()];
        // Since GC can make `clauses` out of date, we need to check its aliveness here.
        if c.is(Flag::DEAD) {
            continue;
        }
        debug_assert!(!c.is(Flag::ELIMINATED));
        let timestamp = c.timestamp();
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
                cdb.garbage_collect();
                return Ok(());
            }
            state.flush(format!(
                "clause vivifying(assert:{}, purge:{} shorten:{}, check:{}/{})...",
                num_assert, num_purge, num_shrink, num_check, num_target,
            ));
            to_display = num_check + display_step;
        }
        num_check += 1;
        'this_clause: for l in clits.iter().map(|ol| *ol) {
            debug_assert_eq!(asg.root_level, asg.decision_level());
            seen[0] = num_check;
            match asg.assigned(l) {
                //
                //## Rule 1
                //
                Some(false) => {
                    // This is not the optimal. But due to implementation of strengthen_by_vivification,
                    // we must keep the literal order.
                    copied.push(l);
                }
                //
                //## Rule 2
                //
                Some(true) => {
                    //
                    // This path is optimized for the case the decision level is zero.
                    //
                    // copied.push(!*l);
                    // let r = asg.reason_literals(cdb, *l);
                    // copied = asg.minimize(cdb, &copied, &r, &mut seen);
                    // if copied.len() == 1 {
                    //     assert_eq!(copied[0], *l);
                    //     copied.clear();
                    // }
                    copied.clear();
                    break 'this_clause;
                }
                None => {
                    copied.push(l);
                    asg.assign_by_decision(!l);
                    let cc: ClauseId = asg.propagate_sandbox(cdb);
                    //
                    //## Rule 3
                    //
                    if !cc.is_none() {
                        break 'this_clause;
                    }

                    //
                    //## Rule 4
                    //
                    // nothing to do
                }
            }
        }
        debug_assert!(!cdb[cs.to()].is(Flag::DEAD));
        match copied.len() {
            0 if timestamp < average_timestamp => {
                cdb.delete_clause(cs.to());
                num_purge += 1;
            }
            0 => (),
            1 => {
                let l0 = copied[0];
                assert_eq!(asg.assigned(l0), Some(false));
                // `asg.assign_at_root_level` calls the normal `cancel_until`.
                // To avoid it, we call `asg.backtrack_sandbox` before it.
                asg.backtrack_sandbox();
                cdb.certificate_add_assertion(l0);
                cdb.delete_clause(cs.to());
                // cdb.garbage_collect();
                assert_eq!(asg.assigned(l0), None);
                asg.assign_at_root_level(l0)?;
                if !asg.propagate_sandbox(cdb).is_none() {
                    // panic!("Vivification found an inconsistency.");
                    return Err(SolverError::Inconsistent);
                }
                num_purge += 1;
                num_assert += 1;
            }
            n if n == clits.len() => (),
            n => {
                if n == 2 && cdb.registered_biclause(copied[0], copied[1]).is_some() {
                    cdb.delete_clause(cs.to());
                    num_purge += 1;
                } else {
                    cdb.strengthen_by_vivification(cs.to(), n);
                    elim.to_simplify += 1.0 / (2 as f64).powf(1.4);
                    num_shrink += 1;
                }
            }
        }
        asg.backtrack_sandbox();
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
    cdb.garbage_collect();
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
        for l in self.stack_iter().rev() {
            if seen[l.vi()] != key {
                continue;
            }
            if lits.contains(l) {
                res.push(!*l);
            } else if lits.contains(&!*l) {
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

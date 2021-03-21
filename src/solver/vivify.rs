//! Vivification
#![allow(dead_code)]
#![cfg(feature = "clause_vivification")]
use {
    super::{restart, Restarter, Stat, State},
    crate::{
        assign::{self, AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{self, ClauseDB, ClauseDBIF, ClauseIF},
        processor::Eliminator,
        state::StateIF,
        types::*,
    },
    std::borrow::Cow,
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
    rst: &mut Restarter,
    state: &mut State,
) -> MaybeInconsistent {
    if rst.derefer(restart::property::Tusize::TriggerLevelMax) <= state.vivify_threshold {
        return Ok(());
    }
    let mut clauses: Vec<OrderedProxy<ClauseId>> = Vec::new();
    {
        let thr = 8 + 22usize.saturating_sub(
            ((asg.derefer(assign::property::Tusize::NumUnassertedVar) as f64).log2()
                + (cdb.derefer(cdb::property::Tusize::NumActive) as f64).log10())
                as usize,
        );
        for (i, c) in cdb.iter().enumerate().skip(1) {
            if c.is(Flag::DEAD) || c.is(Flag::VIVIFIED) {
                continue;
            }
            if let Some(act) = c.to_vivify(thr) {
                clauses.push(OrderedProxy::new(ClauseId::from(i), -act));
            }
        }
    }
    if clauses.is_empty() {
        return Ok(());
    }
    clauses.sort_unstable();
    let num_target = clauses.len();
    state[Stat::Vivification] += 1;
    let dl = asg.decision_level();
    debug_assert_eq!(dl, 0);
    // This is a reusable vector to reduce memory consumption, the key is the number of invocation
    let mut seen: Vec<usize> = vec![0; asg.num_vars + 1];
    let display_step: usize = 1000;
    let mut num_check = 0;
    let mut num_purge = 0;
    let mut num_shrink = 0;
    let mut num_assert = 0;
    let mut to_display = 0;

    while let Some(cs) = clauses.pop() {
        let activity = cdb.activity(cs.to());
        let c: &mut Clause = &mut cdb[cs.to()];
        // Since GC can make `clauses` out of date, we need to check its aliveness here.
        if c.is(Flag::DEAD) {
            continue;
        }
        let is_learnt = c.is(Flag::LEARNT);
        c.vivified();
        let clits = c.lits.clone();
        let mut copied: Vec<Lit> = Vec::new();
        let mut flipped = true;
        if to_display <= num_check {
            state.flush("");
            state.flush(format!(
                "clause vivifying(assert:{}, purge:{} shorten:{}, check:{}/{})...",
                num_assert, num_purge, num_shrink, num_check, num_target,
            ));
            to_display = num_check + display_step;
        }
        num_check += 1;
        'this_clause: for l in clits.iter().map(|ol| *ol) {
            debug_assert_eq!(0, asg.decision_level());
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
                    flipped = false;
                    break 'this_clause;
                }
                None => {
                    let cid: Option<ClauseId> = match copied.len() {
                        0 => None,
                        1 => {
                            debug_assert!(flipped);
                            debug_assert_eq!(asg.assigned(copied[0]), None);
                            debug_assert_eq!(0, asg.decision_level());
                            asg.assign_by_decision(copied[0]);
                            None
                        }
                        _ => {
                            let cid = cdb.new_clause_sandbox(asg, &mut copied.clone());
                            Some(cid)
                        }
                    };
                    debug_assert_eq!(asg.assigned(!l), None);
                    asg.assign_by_decision(!l);
                    let cc: ClauseId = asg.propagate_sandbox(cdb);
                    //
                    //## Rule 3
                    //
                    if !cc.is_none() {
                        copied.push(!l);
                        copied = asg.analyze(cdb, &copied, &cdb[cc].lits, &mut seen);
                        // this reverts dda678e
                        // Here we found an inconsistency.
                        // So we can abort this function without rolling back to level zero.
                        if copied.is_empty() {
                            break 'this_clause;
                        }
                        flipped = false;
                    }
                    asg.backtrack_sandbox();
                    if let Some(cj) = cid {
                        debug_assert!(cdb[cj].is(Flag::VIV_ASSUMED));
                        cdb.detach(cj);
                        debug_assert!(!asg.locked(&cdb[cj], cj));
                        cdb.garbage_collect();
                        debug_assert!(cdb[cj].is(Flag::DEAD));
                    }
                    if !cc.is_none() {
                        break 'this_clause;
                    }
                    //
                    //## Rule 4
                    //
                    copied.push(!l);
                }
            }
        }
        if flipped {
            flip(&mut copied);
        }
        match copied.len() {
            0 if flipped => {
                cdb.garbage_collect();
                cdb.certificate_add(&[clits[0], clits[1]]);
                debug_assert!(asg.stack_iter().all(|l| asg.assigned(*l).is_some()));
                return Err(SolverError::Inconsistent);
            }
            0 => {
                if !cdb[cs.to()].is(Flag::DEAD) {
                    cdb.detach(cs.to());
                    cdb.garbage_collect();
                    num_purge += 1;
                }
            }
            1 => {
                let l0 = copied[0];
                debug_assert_ne!(asg.assigned(l0), Some(false));
                debug_assert_eq!(asg.decision_level(), asg.root_level);
                if asg.assigned(l0) == None {
                    num_assert += 1;
                    cdb.certificate_add(&copied);
                    asg.assign_at_root_level(l0)?;
                    if !asg.propagate_sandbox(cdb).is_none() {
                        // panic!("Vivification found an inconsistency.");
                        cdb.garbage_collect();
                        return Err(SolverError::Inconsistent);
                    }
                }
                debug_assert!(!cdb[cs.to()].is(Flag::DEAD));
                cdb.detach(cs.to());
                num_purge += 1;
            }
            n if n == clits.len() => (),
            n => {
                if n == 2 && cdb.registered_bin_clause(copied[0], copied[1]) {
                    num_purge += 1;
                } else {
                    cdb.certificate_add(&copied);
                    let cj = cdb.new_clause(asg, &mut copied, is_learnt, true);
                    cdb.set_activity(cj, activity);
                    cdb[cj].turn_on(Flag::VIVIFIED);
                    num_shrink += 1;
                }
                elim.to_simplify += 1.0 / (n as f64).powf(1.4);
                debug_assert!(!cdb[cs.to()].is(Flag::DEAD));
                cdb.detach(cs.to());
            }
        }
    }
    state.log(
        state[Stat::Vivification],
        format!(
            "vivify lv:{:>4}, pick:{:>6}, var:{:>4}, purge:{:>4}, shrink:{:>4}",
            state.vivify_threshold, num_check, num_assert, num_purge, num_shrink,
        ),
    );
    state[Stat::VivifiedClause] += num_shrink + num_purge;
    state[Stat::VivifiedVar] += num_assert;
    cdb.garbage_collect();
    state.vivify_threshold = rst.derefer(restart::property::Tusize::TriggerLevelMax);
    Ok(())
}

fn flip(vec: &mut [Lit]) -> &mut [Lit] {
    for l in vec.iter_mut() {
        *l = !*l;
    }
    vec
}

impl AssignStack {
    fn reason_literals<'a>(&self, cdb: &'a ClauseDB, l: Lit) -> Cow<'a, Vec<Lit>> {
        match self.reason(l.vi()) {
            AssignReason::Implication(cid, _) => Cow::Borrowed(&cdb[cid].lits),
            AssignReason::None => Cow::Owned(vec![l]),
        }
    }
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
            for r in self.reason_literals(cdb, *l).iter() {
                seen[r.vi()] = key;
            }
        }
        res
    }
}

//! Vivification
#![allow(dead_code)]
use {
    super::{SolverEvent, Stat, State},
    crate::{
        assign::{AssignIF, AssignStack, ClauseManipulateIF, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        processor::Eliminator,
        state::StateIF,
        types::*,
    },
    std::borrow::Cow,
};

/// vivify clauses in `cdb` under `asg`
pub fn vivify(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
) -> MaybeInconsistent {
    let mut clauses: Vec<ClauseId> = Vec::new();
    for (i, c) in cdb.iter_mut().enumerate().skip(1) {
        if c.len() == c.rank as usize && c.to_vivify() {
            clauses.push(ClauseId::from(i));
        }
    }
    // clauses.sort_by_cached_key(|cid| cdb[*cid].rank);
    // clauses.resize(clauses.len() / num_to_vivify, ClauseId::default());
    let num_target = clauses.len();
    if num_target == 0 {
        return Ok(());
    }
    asg.handle(SolverEvent::Vivify(true));
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
    let mut to_display = display_step;

    while let Some(ci) = clauses.pop() {
        let c: &mut Clause = &mut cdb[ci];
        // Since GC can make `clauses` out of date, we need to check its aliveness here.
        if c.is(Flag::DEAD) {
            continue;
        }
        c.turn_on(Flag::VIVIFIED);
        c.turn_off(Flag::VIVIFIED2);
        let is_learnt = c.is(Flag::LEARNT);
        if !is_learnt {
            c.turn_off(Flag::DERIVE20);
        }
        let clits = c.lits.clone();
        let mut copied: Vec<Lit> = Vec::new();
        let mut flipped = true;
        // elim.eliminate_satisfied_clauses(asg, cdb, false);
        num_check += 1;
        'this_clause: for l in clits.iter() {
            debug_assert_eq!(0, asg.decision_level());
            seen[0] = num_check;
            if to_display <= num_check {
                state.flush("");
                state.flush(format!(
                    "vivifying(assert:{}, purge:{} shorten:{}, check:{}/{})...",
                    num_assert, num_purge, num_shrink, num_check, num_target,
                ));
                to_display = num_check + display_step;
            }
            match asg.assigned(*l) {
                // Rule 1
                Some(false) => continue 'this_clause,
                // Rule 2
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
                            cdb.handle(SolverEvent::Vivify(true));
                            debug_assert!(cdb.during_vivification);
                            let cid = cdb.new_clause(asg, &mut copied.clone(), true, false);
                            cdb.handle(SolverEvent::Vivify(false));
                            Some(cid)
                        }
                    };
                    debug_assert_eq!(asg.assigned(!*l), None);
                    asg.assign_by_decision(!*l);
                    let cc: ClauseId = asg.propagate(cdb);
                    // Rule 3
                    if !cc.is_none() {
                        copied.push(!*l);
                        copied = asg.analyze(cdb, &copied, &cdb[cc].lits, &mut seen);
                        // this reverts dda678e
                        // Here we found an inconsistency.
                        // So we can abort this function without rolling back to level zero.
                        if copied.is_empty() {
                            break 'this_clause;
                        }
                        flipped = false;
                    }
                    asg.cancel_until(asg.root_level);
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
                    // Rule 4
                    copied.push(!*l);
                }
            }
        }
        if flipped {
            flip(&mut copied);
        }
        match copied.len() {
            0 if flipped => {
                cdb.certificate_add(&clits[0..1]);
                debug_assert!(asg.stack_iter().all(|l| asg.assigned(*l).is_some()));
                return Err(SolverError::Inconsistent);
            }
            0 => {
                if !cdb[ci].is(Flag::DEAD) {
                    cdb.detach(ci);
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
                    if !asg.propagate(cdb).is_none() {
                        // panic!("Vivification found an inconsistency.");
                        return Err(SolverError::Inconsistent);
                    }
                    state[Stat::VivifiedVar] += 1;
                }
                debug_assert!(!cdb[ci].is(Flag::DEAD));
                cdb.detach(ci);
                cdb.garbage_collect();
            }
            n if n == clits.len() => (),
            n => {
                num_shrink += 1;
                if n == 2 && cdb.registered_bin_clause(copied[0], copied[1]) {
                    // num_purge += 1;
                    elim.to_simplify += 1.0;
                } else {
                    cdb.certificate_add(&copied);
                    cdb.handle(SolverEvent::Vivify(true));
                    let cj = cdb.new_clause(asg, &mut copied, is_learnt, true);
                    cdb.handle(SolverEvent::Vivify(false));
                    cdb[cj].turn_on(Flag::VIVIFIED);
                    elim.to_simplify += 1.0 / ((n - 1) as f64).powf(1.6);
                    debug_assert!(!cdb[ci].is(Flag::DEAD));
                    cdb.detach(ci);
                    cdb.garbage_collect();
                }
            }
        }
        clauses.retain(|ci| !cdb[ci].is(Flag::DEAD));
    }
    asg.handle(SolverEvent::Vivify(false));
    if 0 < num_assert || 0 < num_purge || 0 < num_shrink {
        state.log(
            state[Stat::Vivification],
            format!(
                "vivification target:{:>4}, assert:{:>4}, purge:{:>4}, shrink:{:>4}",
                num_check, num_assert, num_purge, num_shrink
            ),
        );
    }
    Ok(())
}

fn flip(vec: &mut [Lit]) -> &mut [Lit] {
    for l in vec.iter_mut() {
        *l = !*l;
    }
    vec
}

impl Clause {
    fn to_vivify(&self) -> bool {
        if self.is(Flag::DEAD) {
            return false;
        }
        self.is(Flag::VIVIFIED) == self.is(Flag::VIVIFIED2)
            && (self.is(Flag::LEARNT) || self.is(Flag::DERIVE20))
    }
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

//! Vivification
#![allow(dead_code)]
use {
    super::{SolverEvent, Stat, State},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        state::StateIF,
        types::*,
    },
    std::{borrow::Cow, collections::HashSet},
};

/// vivify clauses in `cdb` under `asg`
pub fn vivify(asg: &mut AssignStack, cdb: &mut ClauseDB, state: &mut State) {
    asg.handle(SolverEvent::Vivify(true));
    state[Stat::Vivification] += 1;
    let display_step: usize = 100;
    let check_thr = state.vivify_thr as usize;
    let mut ncheck = 0;
    let mut nclause = 0;
    let mut npurge = 0;
    let mut nshrink = 0;
    let mut nassert = 0;
    let mut to_display = display_step;
    debug_assert_eq!(asg.decision_level(), asg.root_level);
    let mut clauses: Vec<ClauseId> = Vec::new();
    for (i, c) in cdb.iter_mut().enumerate().skip(1) {
        if c.to_vivify() {
            clauses.push(ClauseId::from(i));
        }
    }
    /*
    clauses.sort_by_cached_key(|c| {
        cdb[c]
            .iter()
            .map(|l| (asg.activity(l.vi()) * -1_000_000.0) as isize)
            .min()
            .unwrap()
    });
    */
    // clauses.sort_by_cached_key(|ci| (cdb.activity(*ci).log(10.0) * -100_000.0) as isize);
    clauses.sort_by_key(|ci| cdb[*ci].rank);
    'next_clause: for ci in clauses.iter() {
        let c: &mut Clause = &mut cdb[ci];
        // Since GC can make `clauses` out of date, we need to check its aliveness here.
        if c.is(Flag::DEAD) {
            continue;
        }
        let is_learnt = c.is(Flag::LEARNT);
        let clits = c.lits.clone();
        drop(c);
        nclause += 1;
        let mut copied: Vec<Lit> = Vec::new();
        for l in clits.iter() {
            ncheck += 1;
            if to_display <= ncheck {
                state.flush("");
                state.flush(format!(
                    "vivifying(assert:{}, purge:{} strengthen:{}, check:{}/{})...",
                    nassert, npurge, nshrink, ncheck, check_thr,
                ));
                to_display = ncheck + display_step;
            }
            match asg.assigned(*l) {
                Some(false) => continue, // Rule 1
                Some(true) => {
                    let r: Vec<Lit> = match asg.reason(l.vi()) {
                        AssignReason::None => Vec::new(),
                        AssignReason::Implication(cid, _) => cdb[cid].lits.to_vec(),
                    };
                    copied.push(*l);
                    copied = asg.minimize(cdb, &copied, &r); // Rule 2
                    #[cfg(debug)]
                    {
                        println!(
                            "\nminimize subclause v:{:?} under satisfied:{}; reason:{:?}",
                            i32s(&copied),
                            !*l,
                            i32s(&r),
                        );
                    }
                    break;
                }
                None => {
                    let cid: Option<ClauseId> = match copied.len() {
                        0 => None,
                        1 => {
                            asg.assign_by_decision(copied[0]);
                            None
                        }
                        _ => Some(cdb.new_clause(asg, &mut copied.clone(), false, true)),
                    };
                    asg.assign_by_decision(!*l);
                    let cc = asg.propagate(cdb);
                    if cc != ClauseId::default() {
                        copied.push(!*l); // Rule 3
                        let mut r = cdb[cc].lits.clone();
                        r.push(!*l);
                        copied = asg.minimize(cdb, &copied, &r);
                        for l in &mut copied {
                            *l = !*l;
                        }
                    } else {
                        copied.push(*l); // Rule 4
                    }
                    asg.cancel_until_sandbox(asg.root_level);
                    if let Some(cj) = cid {
                        cdb.detach(cj);
                        cdb.garbage_collect();
                    }
                    if cc != ClauseId::default() {
                        #[cfg(debug)]
                        if copied.len() <= 1 {
                            println!(
                                "\nAssign:{:?} by propagating:{} @{}; conf:{}",
                                i32s(&copied),
                                !*l,
                                i,
                                &cdb[cc],
                            );
                        }
                        break;
                    }
                }
            }
        }
        match copied.len() {
            0 => {
                // Is this possible? The only posibility is the clause is falsified.
                // This mean we find the CNF is unsatisfiable.
                // So terminate vivification immediately and put the responsibility on solver!
                npurge += 1;
                break 'next_clause;
            }
            1 => {
                nassert += 1;
                debug_assert_eq!(asg.root_level, asg.decision_level());
                asg.assign_at_rootlevel(copied[0]).expect("impossible");
                asg.handle(SolverEvent::Fixed);
                // if asg.propagate(cdb) != ClauseId::default() {
                //     panic!("## propagate emits a conflict.");
                // }
            }
            n => {
                let cj = cdb.new_clause(asg, &mut copied, is_learnt, true);
                // cdb.set_activity(cj, reward);
                if n < clits.len() {
                    nshrink += 1;
                } else {
                    cdb[cj].turn_on(Flag::VIVIFIED);
                }
            }
        }
        cdb.detach(*ci);
        cdb.garbage_collect();
        if check_thr <= ncheck {
            break;
        }
    }
    if state.config.vivify_end <= state.vivify_thr {
        state.vivify_thr = state.config.vivify_beg;
    } else {
        state.vivify_thr *= 2.0;
    }
    state.flush("");
    state.flush(format!(
        "vivified(assert:{} of literals:{}; purge:{} strengthen:{} of clauses:{})...",
        nassert, ncheck, npurge, nshrink, nclause,
    ));
    asg.handle(SolverEvent::Vivify(false));
}

impl Clause {
    fn to_vivify(&mut self) -> bool {
        if self.is(Flag::DEAD) {
            return false;
        }
        if self.is(Flag::VIVIFIED) == self.is(Flag::VIVIFIED2) {
            self.turn_on(Flag::VIVIFIED);
            self.turn_off(Flag::VIVIFIED2);
            if self.is(Flag::LEARNT) {
                return true;
            } else if self.is(Flag::DERIVE20) {
                self.turn_off(Flag::DERIVE20);
                return true;
            }
        }
        false
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
    fn minimize(&mut self, cdb: &ClauseDB, lits: &[Lit], reason: &[Lit]) -> Vec<Lit> {
        let mut seen: HashSet<Lit> = HashSet::new();
        let mut res: Vec<Lit> = Vec::new();
        for l in reason {
            seen.insert(*l);
        }
        for l in self.stack_iter().rev() {
            // l is a negated literal
            if !seen.contains(&!*l) && !seen.contains(l) {
                continue;
            }
            if lits.contains(l) || lits.contains(&!*l) {
                res.push(*l);
                continue;
            }
            for r in self.reason_literals(cdb, *l).iter() {
                seen.insert(*r);
                seen.insert(!*r);
            }
        }
        /*
        if reason.len() == 2 {
            println!(
                "{:?} /\\ {} {:?} => {:?}",
                clause,
                if let Some(_) = self.assigned(clause[0]) {
                    "assigned"
                } else {
                    "unassigned"
                },
                reason,
                res
            );
        }
        */
        res
    }
}

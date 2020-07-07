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
    std::borrow::Cow,
};

/// vivify clauses in `cdb` under `asg`
pub fn vivify(asg: &mut AssignStack, cdb: &mut ClauseDB, state: &mut State) {
    asg.handle(SolverEvent::Vivify(true));
    state[Stat::Vivification] += 1;
    let mut seen: Vec<usize> = vec![0; asg.num_vars + 1];
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
    for ci in clauses.iter() {
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
        let mut flipped = true;
        'this_clause: for l in clits.iter() {
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
                Some(false) => continue 'this_clause, // Rule 1
                Some(true) => {
                    copied.push(!*l);
                    let r = asg.reason_literals(cdb, *l);
                    copied = asg.minimize(cdb, &copied, &r, ncheck, &mut seen); // Rule 2
                    debug_assert_eq!(copied[0], *l);
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
                        _ => Some(cdb.new_clause(asg, &mut copied.clone(), false, true)),
                    };
                    asg.assign_by_decision(!*l);
                    let cc = asg.propagate(cdb);
                    // debug_assert!(flipped);
                    copied.push(!*l); // Rule 4
                    if cc != ClauseId::default() {
                        let r = cdb[cc].lits.clone(); // Rule 3
                        copied = asg.minimize(cdb, &copied, &r, ncheck, &mut seen);
                        flipped = false;
                    }
                    asg.cancel_until_sandbox(asg.root_level);
                    if let Some(cj) = cid {
                        cdb.detach(cj);
                        cdb.garbage_collect();
                    }
                    if cc != ClauseId::default() {
                        break 'this_clause;
                    }
                }
            }
        }
        if flipped {
            flip(&mut copied);
        }
        match copied.len() {
            0 => {
                // Is this possible? The only posibility is the clause is falsified.
                // This mean we find the CNF is unsatisfiable.
                // So terminate vivification immediately and put the responsibility on solver!
                npurge += 1;
            }
            1 => {
                nassert += 1;
                // assert_eq!(asg.root_level, asg.decision_level());
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

fn flip(vec: &mut [Lit]) -> &mut [Lit] {
    for l in vec.iter_mut() {
        *l = !*l;
    }
    vec
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
    fn minimize(
        &mut self,
        cdb: &ClauseDB,
        lits: &[Lit],
        reason: &[Lit],
        id: usize,
        seen: &mut [usize],
    ) -> Vec<Lit> {
        let mut res: Vec<Lit> = Vec::new();
        for l in reason {
            seen[l.vi()] = id;
        }
        for l in self.stack_iter().rev() {
            if seen[l.vi()] != id {
                continue;
            }
            if lits.contains(l) {
                res.push(!*l);
                continue;
            }
            if lits.contains(&!*l) {
                res.push(*l);
                continue;
            }
            for r in self.reason_literals(cdb, *l).iter() {
                seen[r.vi()] = id;
            }
        }
        res
    }
}

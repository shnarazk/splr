//! Vivification
#![allow(dead_code)]
use {
    super::{SolverEvent, Stat, State},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarRewardIF},
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
    let mut nclause_new = 0;
    let mut nclause_vivified = 0;
    let mut npurge = 0;
    let mut nshrink = 0;
    let mut nassert = 0;
    let mut to_display = display_step;
    debug_assert_eq!(asg.decision_level(), asg.root_level);
    // if asg.propagate(cdb) != ClauseId::default() {
    //     panic!("eabarmbrr");
    // }
    let mut clauses: Vec<ClauseId> = Vec::new();
    for (i, c) in cdb.iter_mut().enumerate().skip(1) {
        if !c.is(Flag::DEAD) && 2 < c.len() {
            clauses.push(ClauseId::from(i));
        }
    }
    clauses.sort_by_cached_key(|c| {
        cdb[c]
            .iter()
            .map(|l| (asg.activity(l.vi()) * 100_000.0) as usize)
            .max()
            .unwrap()
    });
    'next_clause: for ci in clauses.iter().rev() {
        let reward = cdb.activity(*ci);
        let c: &Clause = &cdb[ci];
        // Since GC can make `clauses` out of date, we need to check its aliveness here.
        if c.is(Flag::DEAD) {
            continue;
        }
        if c.is(Flag::VIVIFIED) {
            nclause_vivified += 1;
            if nclause_new / 2 < nclause_vivified {
                continue;
            }
        } else {
            nclause_new += 1;
        }
        let is_learnt = c.is(Flag::LEARNT);
        let clits = c.lits.clone();
        let mut v: Vec<Lit> = Vec::new();
        let mut vivified: Vec<Lit> = Vec::new();
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
                Some(true) => {
                    let r: Vec<Lit> = match asg.reason(l.vi()) {
                        AssignReason::None => Vec::new(),
                        AssignReason::Implication(cid, _) => cdb[cid].lits.to_vec(),
                    };
                    // for lit in &mut r {
                    //     if *lit == *l {
                    //        *lit = !*l;
                    //        break;
                    //     }
                    // }
                    v.push(*l);
                    vivified = asg.minimize(cdb, &v, &r); // Rule 2
                    #[cfg(debug)]
                    {
                        println!(
                            "\nminimize subclause v:{:?} to {:?} under satisfied:{}; reason:{:?}",
                            i32s(&v),
                            i32s(&vivified),
                            !*l,
                            i32s(&r),
                        );
                    }
                    if vivified.is_empty() {
                        npurge += 1;
                        cdb.detach(*ci);
                        cdb.garbage_collect();
                        continue 'next_clause;
                    }
                    break;
                    // state.flush(".");
                    //continue 'next_clause;
                }
                Some(false) => {
                    continue;
                    //v.push(!*l);                          // Rule 4
                }
                None => {
                    let cid: Option<ClauseId> = match v.len() {
                        0 => None,
                        1 => {
                            asg.assign_by_decision(v[0]);
                            None
                        }
                        _ => Some(cdb.new_clause(asg, &mut v.clone(), false, true)), // L.12
                    };
                    asg.assign_by_decision(!*l);
                    let cc = asg.propagate(cdb);
                    if cc != ClauseId::default() {
                        v.push(!*l);
                        let mut r = cdb[cc].lits.clone();
                        r.push(!*l);
                        vivified = asg.minimize(cdb, &v, &r); // Rule 3
                        for l in &mut vivified {
                            *l = !*l;
                        }
                    /*
                    assert!(avivified.iter().all(|l| v.contains(l)),
                            format!("{:?} + {:?} => {:?}",
                                    v,
                                    cdb[cc].lits,
                                    avivified,
                                    ),
                    );
                    */
                    } else {
                        v.push(*l);
                    }
                    if let Some(cj) = cid {
                        cdb.detach(cj);
                        cdb.garbage_collect();
                    }
                    asg.cancel_until_sandbox(asg.root_level);
                    if cc != ClauseId::default() {
                        #[cfg(debug)]
                        if vivified.len() <= 1 {
                            println!(
                                "\nAssign:{:?} from assumed v:{:?} propagating:{} @{}; conf:{}",
                                i32s(&vivified),
                                i32s(&v),
                                !*l,
                                i,
                                &cdb[cc],
                            );
                        }
                        break; // continue 'next_clause;
                    }
                }
            }
        }
        if vivified.is_empty() {
            // for l in &mut v {
            //     *l = !*l;
            // }
            std::mem::swap(&mut vivified, &mut v);
        }
        match vivified.len() {
            0 => {
                // Is this possible? The only posibility is the clause is falsified.
                // This mean we find the CNF is unsatisfiable.
                // So terminate vivification immediately and put the responsibility on solver!
                break 'next_clause;
            }
            1 => {
                nassert += 1;
                assert_eq!(asg.root_level, asg.decision_level());
                asg.assign_at_rootlevel(vivified[0]).expect("impossible");
                asg.handle(SolverEvent::Fixed);
                // if asg.propagate(cdb) != ClauseId::default() {
                //     panic!("## propagate emits a conflict.");
                // }
            }
            n => {
                if n < clits.len() {
                    nshrink += 1;
                }
                let cj = cdb.new_clause(asg, &mut vivified, is_learnt, true);
                cdb.set_activity(cj, reward);
                cdb[cj].turn_on(Flag::VIVIFIED);
            }
        }
        cdb.detach(*ci);
        cdb.garbage_collect();
        if check_thr < ncheck {
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
        nassert,
        ncheck,
        npurge,
        nshrink,
        nclause_new + nclause_vivified,
    ));
    asg.handle(SolverEvent::Vivify(false));
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

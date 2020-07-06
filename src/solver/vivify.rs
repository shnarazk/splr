//! Vivification
#![allow(dead_code)]
use {
    super::{conflict::conflict_analyze_sandbox, SolverEvent, Stat, State},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF, VarRewardIF},
        cdb::{ClauseDB, ClauseDBIF},
        state::StateIF,
        types::*,
    },
    std::{borrow::Cow, collections::HashSet},
};

pub fn vivify_old(asg: &mut AssignStack, cdb: &mut ClauseDB, state: &mut State) {
    asg.handle(SolverEvent::Vivify(true));
    state[Stat::Vivification] += 1;
    let display_step: usize = 1_000;
    let check_thr = state.vivify_thr as usize;
    let mut ncheck = 0;
    let mut nclause = 0;
    let mut nshrink = 0;
    let mut nassign = 0;
    let mut to_display = display_step;
    debug_assert_eq!(asg.decision_level(), asg.root_level);
    'check_loop: loop {
        let mut changed: bool = false;
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
        for ci in clauses.iter().rev() {
            let reward = cdb.activity(*ci);
            let c: &Clause = &cdb[ci];
            // Since GC can make `clauses` out of date, we need to check its aliveness here.
            if c.is(Flag::DEAD) {
                continue;
            }
            nclause += 1;
            let is_learnt = c.is(Flag::LEARNT);
            let clits = c.lits.clone();
            let c_len = clits.len();
            cdb.detach(*ci);
            cdb.garbage_collect();
            let mut shortened = false;
            let mut new_clause: Vec<Lit> = Vec::new();
            for (i, l) in clits.iter().enumerate() {
                if asg.assigned(*l).is_some() {
                    continue;
                }
                ncheck += 1;
                if to_display <= ncheck {
                    state.flush("");
                    state.flush(format!(
                        "vivifying(fix:{}, strengthen:{}/{}, check:{}/{})...",
                        nassign, nshrink, nclause, ncheck, check_thr,
                    ));
                    to_display = ncheck + display_step;
                }
                asg.assign_by_decision(!*l);
                let confl = asg.propagate(cdb);
                if confl != ClauseId::default() {
                    conflict_analyze_sandbox(asg, cdb, state, confl);
                    let learnt = &state.new_learnt;
                    if learnt.iter().all(|l| clits.contains(l)) {
                        new_clause = learnt.clone();
                        shortened = true;
                    } else {
                        if learnt.len() < c_len {
                            assert!(new_clause.is_empty());
                            new_clause = learnt.clone();
                            // asg.cancel_until_sandbox(asg.root_level);
                            break;
                        }
                        if i < c_len - 1 {
                            new_clause = clits[..=i].to_vec();
                            shortened = true;
                        }
                    }
                } else if let Some(ls) = clits[i + 1..]
                    .iter()
                    .find(|l| asg.assigned(**l) == Some(true))
                {
                    if i < c_len - 1 {
                        new_clause = clits[..=i].to_vec();
                        new_clause.push(*ls);
                        shortened = true;
                    }
                } else if let Some(ls) = clits[i + 1..]
                    .iter()
                    .find(|l| asg.assigned(!**l) == Some(true))
                {
                    new_clause = clits
                        .iter()
                        .copied()
                        .filter(|l| l != ls)
                        .collect::<Vec<_>>();
                    shortened = true;
                }
                // asg.cancel_until_sandbox(asg.root_level);
                // debug_assert!(asg.assigned(*l).is_none());
                if shortened {
                    break;
                }
            }
            asg.cancel_until_sandbox(asg.root_level);
            if !new_clause.is_empty() {
                if new_clause.len() == 1 {
                    nassign += 1;
                    asg.assign_at_rootlevel(new_clause[0]).expect("impossible");
                    asg.handle(SolverEvent::Fixed);
                } else {
                    nshrink += 1;
                    cdb.new_clause(asg, &mut new_clause, is_learnt, false);
                }
            }
            if shortened {
                changed = true;
            } else {
                let mut cls = clits.clone();
                let cj = cdb.new_clause(asg, &mut cls, false, false);
                cdb.set_activity(cj, reward);
            }
            if check_thr < ncheck {
                break 'check_loop;
            }
        }
        if !changed {
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
        "vivified(fix:{} & strengthen:{} of clauses:{})...",
        nassign, nshrink, nclause,
    ));
    asg.handle(SolverEvent::Vivify(false));
}

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
        nclause += 1;
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
        nassert, ncheck, npurge, nshrink, nclause,
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

//! Vivification
#![allow(dead_code)]
#[cfg(feature = "libc")]
use std::{thread, time::Duration};
use {
    super::{SolverEvent, Stat, State},
    crate::{
        assign::{AssignIF, AssignStack, ClauseManipulateIF, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        processor::Eliminator,
        state::StateIF,
        types::*,
    },
    std::{
        borrow::Cow,
        sync::{
            atomic::{AtomicBool, Ordering},
            Arc,
        },
    },
};

/// vivify clauses in `cdb` under `asg`
pub fn vivify(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
) -> MaybeInconsistent {
    asg.handle(SolverEvent::Vivify(true));
    state[Stat::Vivification] += 1;
    let dl = asg.decision_level();
    assert_eq!(dl, 0);
    // This is a reusable vector to reduce memory consumption, the key is the number of invocation
    let mut seen: Vec<usize> = vec![0; asg.num_vars + 1];
    let check_thr = (state.vivify_thr * 10_000_000.0 / asg.var_stats().3 as f64) as usize;
    let timedout = Arc::new(AtomicBool::new(false));
    #[cfg(feature = "libc")]
    {
        // The ratio of time slot for single elimination step.
        // Since it is measured in millisecond, 1000 means executing elimination
        // until timed out. 100 means this function can consume 10% of a given time.
        let timeslot_for_vivification: u64 = state.vivify_thr as u64;
        let timedout2 = timedout.clone();
        let time = timeslot_for_vivification * state.config.c_tout as u64;
        thread::spawn(move || {
            thread::sleep(Duration::from_millis(time));
            timedout2.store(true, Ordering::Release);
        });
    }
    // {
    // let k = state.config.timeout / (asg.var_stats().3 as f64).sqrt();
    //     panic!("{}| check {:.1} - {:.1}",
    //            (cdb.count() as f64).sqrt(),
    //            state.config.vivify_beg * k,
    //            state.config.vivify_end * k,
    //     );
    // }
    let display_step: usize = 250.max(check_thr / 5);
    let mut ncheck = 0;
    let mut npurge = 0;
    let mut nshrink = 0;
    let mut nassert = 0;
    let mut to_display = display_step;
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
    clauses.resize(clauses.len() / 2, ClauseId::default());
    assert!(!asg.remains());
    'next_clause: while let Some(ci) = clauses.pop() {
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
        // cdb.eliminate_satisfied_clauses(asg, elim, false);
        cdb.garbage_collect();
        'this_clause: for l in clits.iter() {
            debug_assert_eq!(0, asg.decision_level());
            ncheck += 1;
            seen[0] = ncheck;
            if to_display <= ncheck {
                state.flush("");
                state.flush(format!(
                    "vivifying(assert:{}, purge:{} shorten:{}, check:{})...",
                    nassert, npurge, nshrink, ncheck,
                ));
                to_display = ncheck + display_step;
            }
            match asg.assigned(*l) {
                Some(false) => continue 'this_clause, // Rule 1
                Some(true) => {
                    assert_eq!(asg.decision_level(), 0);
                    // copied.push(!*l);
                    // let r = asg.reason_literals(cdb, *l);
                    // copied = asg.minimize(cdb, &copied, &r, &mut seen); // Rule 2
                    state.viv_pathes[8 + copied.len().min(2)] = true;
                    // if copied.len() == 1 {
                    //     assert_eq!(copied[0], *l);
                    //     copied.clear();
                    // }
                    //                    continue 'this_clause;
                    copied.clear();
                    flipped = false;
                    break 'this_clause;
                }
                None => {
                    let cid: Option<ClauseId> = match copied.len() {
                        0 => None,
                        1 => {
                            assert!(flipped);
                            assert_eq!(asg.assigned(copied[0]), None);
                            assert_eq!(0, asg.decision_level());
                            asg.assign_by_decision(copied[0]);
                            None
                        }
                        _ => {
                            // continue 'next_clause;
                            cdb.handle(SolverEvent::Vivify(true));
                            assert!(cdb.during_vivification);
                            let cid = cdb.new_clause(asg, &mut copied.clone(), true, false);
                            cdb.handle(SolverEvent::Vivify(false));
                            Some(cid)
                        }
                    };
                    assert_eq!(asg.assigned(!*l), None);
                    asg.assign_by_decision(!*l);
                    let cc: ClauseId = asg.propagate(cdb);
                    if !cc.is_none() {
                        copied.push(!*l);
                        let r = cdb[cc].lits.clone(); // Rule 3
                        let result = asg.analyze(cdb, &copied, &r, &mut seen);
                        if result.is_empty() {
                            break 'this_clause;
                        }
                        assert!(result.contains(l));
                        copied.clear();
                        copied.push(*l);
                        for lit in &result {
                            if *lit != *l {
                                copied.push(*lit);
                            }
                        }
                        // copied = result;
                        flipped = false;
                    }
                    asg.cancel_until(asg.root_level);
                    if let Some(cj) = cid {
                        debug_assert!(cdb[cj].is(Flag::VIV_ASSUMP));
                        cdb.detach(cj);
                        debug_assert!(!asg.locked(&cdb[cj], cj));
                        cdb.garbage_collect();
                        debug_assert!(cdb[cj].is(Flag::DEAD));
                    }
                    if !cc.is_none() {
                        break 'this_clause;
                    }
                    copied.push(!*l); // Rule 4
                }
            }
        }
        if flipped {
            flip(&mut copied);
        }
        match copied.len() {
            0 if flipped => {
                state.viv_pathes[0] = true;
                cdb.certificate_add(&clits[0..1]);
                assert!(asg.stack_iter().all(|l| asg.assigned(*l).is_some()));
                return Err(SolverError::Inconsistent);
            }
            0 => {
                state.viv_pathes[1] = true;
                if !cdb[ci].is(Flag::DEAD) {
                    cdb.detach(ci);
                    cdb.garbage_collect();
                    npurge += 1;
                    elim.to_simplify += 1.0;
                }
            }
            1 => {
                let l0 = copied[0];
                assert_ne!(asg.assigned(l0), Some(false));
                assert_eq!(asg.decision_level(), asg.root_level);
                if asg.assigned(l0) == None {
                    nassert += 1;
                    cdb.certificate_add(&copied);
                    // cdb.certificate_delete(&copied);
                    asg.assign_at_rootlevel(l0)?;
                    if !asg.propagate(cdb).is_none() {
                        state.viv_pathes[2] = true;
                        // panic!("Vivification found an inconsistency. len: {}", clits.len());
                        return Err(SolverError::Inconsistent);
                    }
                    asg.handle(SolverEvent::Assert);
                    elim.to_simplify += 2.0;
                    state[Stat::VivifiedVar] += 1;
                    state.viv_pathes[3] = true;
                } else {
                    state.viv_pathes[4] = true;
                }
                assert!(!cdb[ci].is(Flag::DEAD));
                cdb.detach(ci);
                cdb.garbage_collect();
            }
            n if n == clits.len() => {
                state.viv_pathes[5] = true;
            }
            n => {
                if n == 2 && cdb.registered_bin_clause(copied[0], copied[1]) {
                    state.viv_pathes[6] = true;
                    npurge += 1;
                    elim.to_simplify += 1.0;
                } else {
                    state.viv_pathes[7] = true;
                    nshrink += 1;
                    cdb.certificate_add(&copied);
                    cdb.handle(SolverEvent::Vivify(true));
                    let cj = cdb.new_clause(asg, &mut copied, is_learnt, true);
                    cdb.handle(SolverEvent::Vivify(false));
                    cdb[cj].turn_on(Flag::VIVIFIED);
                    elim.to_simplify += 1.0 / (n - 1) as f64;
                    assert!(!cdb[ci].is(Flag::DEAD));
                    cdb.detach(ci);
                    cdb.garbage_collect();
                }
            }
        }
        if timedout.load(Ordering::Acquire) {
            break;
        }
        #[cfg(not(feature = "libc"))]
        {
            if check_thr <= ncheck {
                break;
            }
        }
        clauses.retain(|ci| !cdb[ci].is(Flag::DEAD));
    }
    if state.config.viv_end <= state.vivify_thr {
        state.vivify_thr = state.config.viv_beg;
    } else {
        state.vivify_thr *= state.config.viv_scale;
    }
    // if 0 < nassert || 0 < npurge || 0 < nshrink {
    //     state.flush("");
    //     state.flush(format!(
    //         "vivified(assert:{}, purge:{}, shorten:{})...",
    //         nassert, npurge, nshrink,
    //     ));
    // }
    asg.handle(SolverEvent::Vivify(false));
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

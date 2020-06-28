//! Vivification
#![allow(dead_code)]
use {
    super::{conflict::conflict_analyze_sandbox, SolverEvent, Stat, State},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        state::StateIF,
        types::*,
    },
    std::collections::HashSet,
};

pub fn vivify(asg: &mut AssignStack, cdb: &mut ClauseDB, state: &mut State) {
    asg.handle(SolverEvent::Vivify(true));
    state[Stat::Vivification] += 1;
    let ncheck_max = 10.0_f64.powf(state.config.vivify_thr) as usize / cdb.count();
    let display_step: usize = 10_000;
    let mut cache: HashSet<Lit> = HashSet::new();
    let mut nseek = 0;
    let mut ncheck = 0;
    let mut nshrink = 0;
    let mut nassign = 0;
    let mut to_display = display_step;
    let mut change: bool = true;
    debug_assert_eq!(asg.decision_level(), asg.root_level);
    while change {
        change = false;
        cache.clear();
        let mut clauses: Vec<ClauseId> = Vec::new();
        for (i, c) in cdb.iter_mut().enumerate().skip(1) {
            if !c.is(Flag::DEAD) && 2 < c.len() {
                clauses.push(ClauseId::from(i));
            }
        }
        // clauses.sort_by_cached_key(|c| 1 - cdb[c].len() as i32);
        clauses.sort_by_cached_key(|c| cdb.activity(*c) as isize);

        for ci in clauses.iter().rev() {
            let c: &Clause = &cdb[ci];
            // Since GC can make `clauses` out of date, we need to check its aliveness here.
            if c.is(Flag::DEAD) {
                continue;
            }
            let is_learnt = c.is(Flag::LEARNT);
            let clits = c.lits.clone();
            let c_len = clits.len();
            cdb.detach(*ci);
            cdb.garbage_collect();
            let mut shortened = false;
            let mut i = 0;
            let mut new_clauses: Vec<Vec<Lit>> = Vec::new();
            let mut reverted = false;
            while !shortened && i < c_len {
                let l = &clits[i]; // select_a_literal(cx);
                i += 1;
                nseek += 1;
                if asg.assigned(*l).is_some() {
                    continue;
                }
                if cache.contains(&!*l) {
                    if !reverted {
                        let mut cls = clits.clone();
                        cdb.new_clause(asg, &mut cls, false, false);
                        reverted = true;
                    }
                    continue;
                }
                ncheck += 1;
                if to_display <= nseek {
                    state.flush("");
                    state.flush(format!(
                        "vivified(fix:{}, strengthen:{}, try:{}, seek:{}, limit:{})...",
                        nassign, nshrink, ncheck, nseek, nseek_max,
                    ));
                    to_display = nseek + display_step;
                }
                asg.assign_by_decision(!*l); // Σb ← (Σb ∪ {¬l})
                let nassign_before_propagation = asg.stack_len();
                let confl = asg.propagate(cdb);
                if confl != ClauseId::default() {
                    // ⊥ ∈ UP(Σb)
                    conflict_analyze_sandbox(asg, cdb, state, confl);
                    let learnt = &state.new_learnt;
                    if learnt.iter().all(|l| clits.contains(l)) {
                        // cl ⊂ c
                        new_clauses.push(learnt.clone()); // MODIFIED: Σ ← Σ ∪ {cl}
                        shortened = true;
                        nshrink += 1;
                        cache.insert(!*l);
                    } else {
                        if learnt.len() < c_len {
                            new_clauses.push(learnt.clone()); // MODIFIED: Σ ← Σ ∪ {cl}
                            i = c_len; // a trick to exit the loop
                        }
                        if c_len != i {
                            let temp = clits[..i].to_vec();
                            debug_assert!(1 < temp.len());
                            new_clauses.push(temp); // MODIFIED: Σ ← Σ ∪ {cb}
                            shortened = true;
                            nshrink += 1;
                            cache.insert(!*l);
                        }
                    }
                } else if asg.stack_len() == nassign_before_propagation {
                    cache.insert(!*l);
                } else {
                    // `i` was incremented.
                    if let Some(ls) = clits[i..].iter().find(|l| asg.assigned(**l) == Some(true)) {
                        // ∃(ls ∈ (c\cb))
                        if 1 < c_len - i {
                            // (c\cb) /= {ls}
                            let mut temp = clits[..i].to_vec();
                            temp.push(*ls);
                            debug_assert!(1 < temp.len());
                            new_clauses.push(temp); // MODIFIED: Σ ← Σ ∪ {cb ∪ {ls}} ;
                            shortened = true;
                            nshrink += 1;
                        }
                    }
                    if let Some(ls) = clits[i..].iter().find(|l| asg.assigned(!**l) == Some(true)) {
                        // ∃(¬Ls ∈ (c\cb))
                        let temp: Vec<Lit> = clits
                            .iter()
                            .copied()
                            .filter(|l| l != ls)
                            .collect::<Vec<_>>();
                        debug_assert!(1 < temp.len());
                        new_clauses.push(temp); // MODIFIED: Σ ← Σ ∪ {c\{ls}}
                        shortened = true;
                        nshrink += 1;
                    }
                }
                if !shortened && !reverted {
                    let mut cls = clits.clone();
                    cdb.new_clause(asg, &mut cls, false, false);
                    reverted = true;
                } else {
                    change = true;
                }
                asg.cancel_until(asg.root_level);
                debug_assert!(asg.assigned(*l).is_none());
            }
            for c in &mut new_clauses {
                if c.len() == 1 {
                    nassign += 1;
                    asg.assign_at_rootlevel(c[0]).expect("impossible");
                    asg.handle(SolverEvent::Fixed);
                } else {
                    cdb.new_clause(asg, c, is_learnt, false);
                }
            }
            if !new_clauses.is_empty() {
                cache.clear();
            }
            if nseek_max < nseek {
                break;
            }
        }
        if nseek_max < nseek {
            change = false;
        }
    }
    state.flush("");
    state.flush(format!(
        "vivified(fix:{}, strengthen:{}, try:{}, seek:{})...",
        nassign, nshrink, ncheck, nseek,
    ));
    asg.handle(SolverEvent::Vivify(false));
}

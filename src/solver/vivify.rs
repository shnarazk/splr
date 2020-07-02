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
};

pub fn vivify(asg: &mut AssignStack, cdb: &mut ClauseDB, state: &mut State) {
    asg.handle(SolverEvent::Vivify(true));
    state[Stat::Vivification] += 1;
    // let ncheck_max = 10.0_f64.powf(state.config.vivify_thr) as usize / cdb.count();
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
        // cdb.activity(*c) as isize);

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
                            asg.cancel_until_sandbox(asg.root_level);
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
                asg.cancel_until_sandbox(asg.root_level);
                debug_assert!(asg.assigned(*l).is_none());
                if shortened {
                    break;
                }
            }
            if shortened {
                if new_clause.len() == 1 {
                    nassign += 1;
                    asg.assign_at_rootlevel(new_clause[0]).expect("impossible");
                    asg.handle(SolverEvent::Fixed);
                } else {
                    nshrink += 1;
                    cdb.new_clause(asg, &mut new_clause, is_learnt, false);
                }
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

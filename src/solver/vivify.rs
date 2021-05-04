//! Vivification
#![allow(dead_code)]
#![cfg(feature = "clause_vivification")]
use {
    super::{restart, Restarter, Stat, State},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{self, ClauseDB, ClauseDBIF, ClauseIF},
        processor::{EliminateIF, Eliminator},
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
    rst: &mut Restarter,
    state: &mut State,
) -> MaybeInconsistent {
    assert_eq!(asg.root_level, asg.decision_level());
    if elim.simplify(asg, cdb, rst, state).is_err() {
        panic!("eaeuae");
    }

    let average_lbd = {
        let ema = rst.refer(restart::property::TEma2::LBD).get();
        if ema.is_nan() {
            -1.0
        } else {
            ema
        }
    };
    let mut clauses: Vec<OrderedProxy<ClauseId>> = gather_clauses(asg, cdb, average_lbd, None);
    if clauses.is_empty() {
        return Ok(());
    }
    let num_target = clauses.len();
    state[Stat::Vivification] += 1;
    debug_assert_eq!(asg.decision_level(), asg.root_level);
    // This is a reusable vector to reduce memory consumption,
    // the key is the number of invocation
    let mut seen: Vec<usize> = vec![0; asg.num_vars + 1];
    let display_step: usize = 1000;
    let mut num_check = 0;
    let mut num_shrink = 0;
    let mut num_assert = 0;
    let mut to_display = 0;
    'next_clause: while let Some(cs) = clauses.pop() {
        assert_eq!(asg.root_level, asg.decision_level());
        let cid = cs.to();
        let activity = cdb.activity(cid);
        let c: &mut Clause = &mut cdb[cid];
        if c.is_dead() || c.is_satisfied_under(asg) {
            continue;
        }
        let is_learnt = c.is(Flag::LEARNT);
        c.vivified();
        let clits = c.iter().map(|l| *l).collect::<Vec<Lit>>();
        let mut decisions: Vec<Lit> = Vec::new();
        if to_display <= num_check {
            state.flush("");
            state.flush(format!(
                "clause vivifying(assert:{} shorten:{}, check:{}/{})...",
                num_assert, num_shrink, num_check, num_target,
            ));
            to_display = num_check + display_step;
        }
        num_check += 1;
        debug_assert!(clits.iter().all(|l| !clits.contains(&!*l)));
        for (i, lit) in clits.clone().iter().map(|p| *p).enumerate() {
            match asg.assigned(!lit) {
                //## Rule 1
                Some(false) => (),
                //## Rule 2
                Some(true) => {
                    asg.backtrack_sandbox();
                    continue 'next_clause;
                }
                //## Rule 3 and 4
                None => {
                    decisions.push(!lit);
                    asg.assign_by_decision(!lit);
                    if let Some(cc) = asg.propagate_sandbox(cdb).to_option() {
                        if cc != cid || i + 1 == clits.len() {
                            asg.backtrack_sandbox();
                            continue 'next_clause;
                        }
                        let conflits = &cdb[cc].iter().map(|l| *l).collect::<Vec<Lit>>();
                        seen[0] = num_check;
                        let mut vec = asg.analyze_sandbox(cdb, &decisions, &conflits, &mut seen);
                        asg.backtrack_sandbox();
                        let new_len = vec.len();
                        if new_len == 1 {
                            let l0 = vec[0];
                            assert_eq!(asg.assigned(l0), None);
                            cdb.certificate_add_assertion(l0);
                            if asg.assign_at_root_level(l0).is_err() {
                                state.log(
                                    asg.num_conflict,
                                    format!(
                                        "(vivify) root level conflict by {} after asserting {}",
                                        cc, l0,
                                    ),
                                );
                                return Err(SolverError::ProcessorFoundUnsat);
                            }
                            num_assert += 1;
                            state[Stat::VivifiedVar] += 1;
                            cdb.remove_clause(cid);
                            if let Some(cc) = asg.propagate(cdb).to_option() {
                                state.log(
                                    asg.num_conflict,
                                    format!("(vivify) root level inconsistency by {} after asserting {}",
                                            cc,
                                            l0,
                                    ),
                                );
                                return Err(SolverError::ProcessorFoundUnsat);
                            }
                            if elim.simplify(asg, cdb, rst, state).is_err() {
                                state.log(
                                    asg.num_conflict,
                                    format!("(vivify) root level inconsistent simplification after asserting {}",
                                            l0,
                                    ),
                                );
                                return Err(SolverError::Inconsistent);
                            }
                            // we must update our `clauses` cynchronously.
                            clauses =
                                gather_clauses(asg, cdb, average_lbd, Some(num_target - num_check));
                        } else {
                            if let Some(ci) = cdb.new_clause(asg, &mut vec, is_learnt).is_new() {
                                cdb.set_activity(ci, activity);
                                cdb[ci].turn_on(Flag::VIVIFIED);
                            }
                            elim.to_simplify += 1.0 / new_len as f64;
                            cdb.remove_clause(cid);
                            num_shrink += 1;
                        }
                        continue 'next_clause;
                    }
                }
            }
        }
        asg.backtrack_sandbox();
        // |TODO| let new_len = decisions.len();
        // |TODO| if 1 < new_len && new_len < clits.len() {
        // |TODO|     flip(&mut decisions);
        // |TODO|     if let Some(ci) = cdb.new_clause(asg, &mut decisions, is_learnt).is_new() {
        // |TODO|         cdb.set_activity(ci, activity);
        // |TODO|         cdb[ci].turn_on(Flag::VIVIFIED);
        // |TODO|     }
        // |TODO|     elim.to_simplify += 1.0 / new_len as f64;
        // |TODO|     num_shrink += 1;
        // |TODO|     cdb.remove_clause(cid);
        // |TODO| }
    }
    state.flush("");
    state.flush(format!(
        "vivified(assert:{} shorten:{}), ",
        num_assert, num_shrink
    ));
    state.log(
        state[Stat::Vivification],
        format!(
            "vivify, pick:{:>8}, assert:{:>6}, shorten:{:>6}",
            num_check, num_assert, num_shrink,
        ),
    );
    state[Stat::VivifiedClause] += num_shrink;
    state[Stat::VivifiedVar] += num_assert;
    Ok(())
}

fn gather_clauses(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    average_lbd: f64,
    max_len: Option<usize>,
) -> Vec<OrderedProxy<ClauseId>> {
    let mut seen = vec![false; 2 * (asg.num_vars + 1)];
    let mut clauses: Vec<OrderedProxy<ClauseId>> = Vec::new();
    if 0.0 < average_lbd {
        let thr = (average_lbd + cdb.derefer(cdb::property::Tf64::DpAverageLBD)) as usize;
        for (i, c) in cdb.iter().enumerate().skip(1) {
            if let Some(act) = c.to_vivify(thr) {
                if true || c.iter().all(|l| !seen[*l]) {
                    for l in c.iter() {
                        seen[*l] = true;
                    }
                    clauses.push(OrderedProxy::new(ClauseId::from(i), -act));
                    if max_len.map_or(false, |thr| thr <= clauses.len()) {
                        break;
                    }
                }
            }
        }
    } else {
        let ml = max_len.map_or(100_000, |thr| thr);
        for (i, c) in cdb.iter().enumerate().skip(1) {
            if true || c.iter().all(|l| !seen[*l]) {
                for l in c.iter() {
                    seen[*l] = true;
                }
                clauses.push(OrderedProxy::new(ClauseId::from(i), -1.0 * c.len() as f64));
                if ml <= clauses.len() {
                    break;
                }
            }
        }
    }
    clauses.sort();
    clauses
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
    fn analyze_sandbox(
        &self,
        cdb: &ClauseDB,
        decisions: &[Lit],
        conflicting: &[Lit],
        seen: &mut [usize],
    ) -> Vec<Lit> {
        let key = seen[0];
        let mut learnt: Vec<Lit> = Vec::new();
        for l in conflicting {
            seen[l.vi()] = key;
        }
        let last_decision = decisions.last().unwrap();
        let from = self.len_upto(self.root_level);
        let all = self.stack_iter().skip(0).map(|l| !*l).collect::<Vec<_>>();
        let assumes = &all[from..];
        debug_assert!(
            all.iter().all(|l| !assumes.contains(&!*l)),
            "vivify252\n{:?}, {:?}",
            assumes
                .iter()
                .filter(|l| all.contains(&!**l))
                .collect::<Vec<_>>(),
            assumes
                .iter()
                .filter(|l| all.contains(&!**l))
                .map(|l| self.reason(l.vi()))
                .collect::<Vec<_>>(),
            // am.iter().filter(|l| am.contains(&!**l)).collect::<Vec<_>>(),
        );
        // sweep in the reverse order
        for l in self.stack_iter().skip(self.len_upto(0)).rev() {
            if seen[l.vi()] != key
            /* || l == last_decision */
            {
                continue;
            }
            if decisions.contains(l) {
                assert!(!learnt.contains(l));
                // Quiz: which is the correct learnt clause here?
                // 1. [decision1, decision2, !last_decision]
                // 2. [!decision1, !decision2, !last_decision]
                // Since `conflict::conflict_analyze` sweeps *reason caluses*,
                // it collects possitive literals in a list. while we collect decision
                // literals in *trail* here. Thus we must negate the literals.
                learnt.push(!*l);
            }
            match self.reason(l.vi()) {
                AssignReason::Implication(_, bil) if bil != NULL_LIT => {
                    seen[bil.vi()] = key;
                }
                AssignReason::Implication(cid, _) => {
                    for r in cdb[cid].iter().skip(1) {
                        seen[r.vi()] = key;
                    }
                }
                _ => (),
            }
        }
        // cnfs/unsat.cnf can panic at
        // 'empty learnt, conflict: [-17L, -5L, 25L, -29L, 50L, 51L, -61L, 63L], assumed: [82L]',
        // src/solver/vivify.rs:312:9

        // make sure the decision var is at the top of list
        // if res.is_empty() {
        //     return
        // }
        debug_assert!(
            !learnt.is_empty(),
            "empty learnt, conflict: {:?}, assumed: {:?}",
            conflicting,
            decisions
        );
        debug_assert!(
            learnt.contains(&!*last_decision),
            "\nThe negation of the last decision {} isn't contained in {:?}",
            last_decision,
            learnt,
        );
        // Since we don't assign the right value of the 'reason' literal after conflict analysis,
        // we need not to swap locations.
        // learnt.swap(0, lst);
        // assert!(matches!(self.reason(learnt[0].vi()), AssignReason::None));
        debug_assert!(
            learnt.iter().all(|l| !learnt.contains(&!*l)),
            "res: {:?} from: {:?} and trail: {:?}",
            learnt,
            decisions,
            assumes,
        );
        learnt
    }
}

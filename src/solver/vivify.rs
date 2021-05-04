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
    elim.simplify(asg, cdb, rst, state)?;
    let ave_lbd = {
        let ema = rst.refer(restart::property::TEma2::LBD).get();
        if ema.is_nan() {
            -1.0
        } else {
            ema
        }
    };
    let mut clauses: Vec<OrderedProxy<ClauseId>> = select(asg, cdb, ave_lbd, None);
    if clauses.is_empty() {
        return Ok(());
    }
    let num_target = clauses.len();
    state[Stat::Vivification] += 1;
    // This is a reusable vector to reduce memory consumption,
    // the key is the number of invocation
    let mut seen: Vec<usize> = vec![0; asg.num_vars + 1];
    let display_step: usize = 1000;
    let mut num_check = 0;
    let mut num_shrink = 0;
    let mut num_assert = 0;
    let mut to_display = 0;
    'next_clause: while let Some(cp) = clauses.pop() {
        let cid = cp.to();
        debug_assert_eq!(asg.root_level, asg.decision_level());
        let c = &mut cdb[cid];
        assert!(!c.is_dead());
        assert!(!c.is_satisfied_under(asg));
        if c.is_dead() || c.is_satisfied_under(asg) {
            continue;
        }
        let is_learnt = c.is(Flag::LEARNT);
        c.vivified();
        let clits = c.iter().map(|l| *l).collect::<Vec<Lit>>();
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
        let mut decisions: Vec<Lit> = Vec::new();
        for lit in clits.iter().take(clits.len() - 1).map(|p| *p) {
            assert!(!asg.var(lit.vi()).is(Flag::ELIMINATED));
            match asg.assigned(!lit) {
                //## Rule 1
                Some(false) => (),
                //## Rule 2
                Some(true) => break,
                //## Rule 3 and 4
                None => {
                    decisions.push(!lit);
                    asg.assign_by_decision(!lit);
                    if let Some(cc) = asg.propagate_sandbox(cdb).to_option() {
                        let conflits = &cdb[cc].iter().map(|l| *l).collect::<Vec<Lit>>();
                        seen[0] = num_check;
                        let mut vec = asg.analyze_sandbox(cdb, &decisions, &conflits, &mut seen);
                        asg.backtrack_sandbox();
                        match vec.len() {
                            0 => {
                                state.flush("");
                                return Err(SolverError::ProcessorFoundUnsat);
                            }
                            1 => {
                                assert_lit(asg, cdb, elim, rst, state, vec[0])?;
                                num_assert += 1;
                                clauses = select(asg, cdb, ave_lbd, Some(num_target - num_check));
                            }
                            n => {
                                if let Some(ci) = cdb.new_clause(asg, &mut vec, is_learnt).is_new()
                                {
                                    cdb.set_activity(ci, cp.value());
                                    cdb[ci].turn_on(Flag::VIVIFIED);
                                }
                                elim.to_simplify += 1.0 / n as f64;
                                if cc == cid {
                                    cdb.remove_clause(cid);
                                    num_shrink += 1;
                                }
                            }
                        }
                        continue 'next_clause;
                    }
                }
            }
        }
        asg.backtrack_sandbox();
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

fn assert_lit(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    rst: &mut Restarter,
    state: &mut State,
    l0: Lit,
) -> MaybeInconsistent {
    assert_eq!(asg.assigned(l0), None);
    cdb.certificate_add_assertion(l0);
    if asg.assign_at_root_level(l0).is_err() {
        state.flush("");
        state.log(
            asg.num_conflict,
            format!("(vivify) root level conflict after asserting {}", l0,),
        );
        return Err(SolverError::ProcessorFoundUnsat);
    }
    state[Stat::VivifiedVar] += 1;
    if let Some(cc) = asg.propagate(cdb).to_option() {
        state.flush("");
        state.log(
            asg.num_conflict,
            format!(
                "(vivify) root level inconsistency by {} after asserting {}",
                cc, l0,
            ),
        );
        return Err(SolverError::ProcessorFoundUnsat);
    }
    if elim.simplify(asg, cdb, rst, state).is_err() {
        state.flush("");
        state.log(
            asg.num_conflict,
            format!(
                "(vivify) root level inconsistent simplification after asserting {}",
                l0,
            ),
        );
        return Err(SolverError::Inconsistent);
    }
    Ok(())
}

fn select(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    thr: f64,
    len: Option<usize>,
) -> Vec<OrderedProxy<ClauseId>> {
    let mut seen = vec![false; 2 * (asg.num_vars + 1)];
    let mut clauses: Vec<OrderedProxy<ClauseId>> = Vec::new();
    if 0.0 < thr {
        let thr = (thr + cdb.derefer(cdb::property::Tf64::DpAverageLBD)) as usize;
        for (i, c) in cdb.iter().enumerate().skip(1) {
            if let Some(act) = c.to_vivify(thr) {
                if !c.is_dead() && c.iter().all(|l| !seen[*l]) {
                    for l in c.iter() {
                        seen[*l] = true;
                    }
                    clauses.push(OrderedProxy::new(ClauseId::from(i), -act));
                    if len.map_or(false, |thr| thr <= clauses.len()) {
                        break;
                    }
                }
            }
        }
    } else {
        let ml = len.map_or(100_000, |thr| thr);
        for (i, c) in cdb.iter().enumerate().skip(1) {
            if !c.is_dead() && c.iter().all(|l| !seen[*l]) {
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
            if seen[l.vi()] != key {
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
        //
        // clause vivifying(assert:0 shorten:0, check:0/12)...thread 'main' panicked at '
        // [-17L, -5L, 25L, -29L, 50L, 51L, -61L, 63L]
        // [Some(false), Some(false), Some(false), Some(false), Some(false), Some(false), Some(false), Some(false)]
        // [0, 0, 0, 0, 0, 0, 0, 0]',
        // src/solver/vivify.rs:297:13
        //
        // This conflicting clause which consists of implicated literals is found
        // befere the target clause made a conflict.
        // So we must skip this conflict.
        if learnt.is_empty() {
            assert_eq!(self.num_conflict, 0);
            // panic!("\n{:?}\n{:?}\n{:?}",
            //        conflicting,
            //        conflicting.iter().map(|l| self.assigned(*l)).collect::<Vec<_>>(),
            //        conflicting.iter().map(|l| self.level(l.vi())).collect::<Vec<_>>(),
            // );
            return learnt;
        }
        // make sure the decision var is at the top of list
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

//! Vivification
#![allow(dead_code)]
use crate::{
    assign::{AssignIF, AssignStack},
    cdb::{clause::ClauseIF, ClauseDB, ClauseDBIF},
    solver::propagate::*,
    state::{Stat, State, StateIF},
    types::*,
};

use super::VarActivityManager;

const VIVIFY_LIMIT: usize = 80_000;

/// vivify clauses under `asg`
fn vivify<'a>(
    vars: &mut [Var<'a>],
    asg: &mut AssignStack<'a>,
    vam: &mut VarActivityManager,
    cdb: &mut ClauseDB<'a>,
    state: &mut State,
) -> MaybeInconsistent {
    const NUM_TARGETS: Option<usize> = Some(VIVIFY_LIMIT);
    if asg.remains() {
        propagate_sandbox(vars, asg, vam, cdb).map_err(|cc| {
            state.log(None, "By vivifier");
            SolverError::RootLevelConflict
        })?;
    }
    let mut clauses: Vec<OrderedProxy<ClauseId>> =
        select_targets(asg, cdb, state[Stat::Restart] == 0, NUM_TARGETS);
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
        backtrack_sandbox(vars, asg, vam);
        debug_assert_eq!(asg.decision_level(), asg.root_level());
        if asg.remains() {
            propagate_sandbox(vars, asg, vam, cdb).map_err(|_| SolverError::RootLevelConflict)?;
        }

        debug_assert!(asg.stack_is_empty() || !asg.remains());
        debug_assert_eq!(asg.root_level(), asg.decision_level());
        let cid = cp.to();
        let c = &mut cdb[cid];
        if c.is_dead() {
            continue;
        }
        let is_learnt = c.is(FlagClause::LEARNT);
        c.vivified();
        let clits = c.iter().copied().collect::<Vec<Lit>>();
        if to_display <= num_check {
            state.flush("");
            state.flush(format!(
                    "clause vivifying(assert:{num_assert} shorten:{num_shrink}, check:{num_check}/{num_target})..."
                ));
            to_display = num_check + display_step;
        }
        num_check += 1;
        debug_assert!(clits.iter().all(|l| !clits.contains(&!*l)));
        let mut decisions: Vec<Lit> = Vec::new();
        for lit in clits.iter().copied() {
            // assert!(!lit.var.is(FlagVar::ELIMINATED));
            match (!lit).assigned() {
                //## Rule 1
                Some(false) => (),
                //## Rule 2
                Some(true) => break,
                None => {
                    decisions.push(!lit);
                    asg.assign_by_decision(!lit);
                    //## Rule 3
                    if let Err(cc) = propagate_sandbox(vars, asg, vam, cdb) {
                        let mut vec: Vec<Lit>;
                        match cc.1 {
                            AssignReason::BinaryLink(l) => {
                                let cnfl_lits = vec![cc.0, !l];
                                // vec = asg.analyze_sandbox(self, &decisions, &cnfl_lits, &mut seen);
                                // asg.backtrack_sandbox();
                                if clits.len() == 2
                                    && cnfl_lits.contains(&clits[0])
                                    && cnfl_lits.contains(&clits[1])
                                {
                                    backtrack_sandbox(vars, asg, vam);
                                    continue 'next_clause;
                                } else {
                                    debug_assert!(clits.len() != 2 || decisions.len() != 2);
                                    seen[0] = num_check;
                                    vec =
                                        asg.analyze_sandbox(cdb, &decisions, &cnfl_lits, &mut seen);
                                    backtrack_sandbox(vars, asg, vam);
                                }
                            }
                            AssignReason::Implication(ci) => {
                                if ci == cid && clits.len() == decisions.len() {
                                    backtrack_sandbox(vars, asg, vam);
                                    continue 'next_clause;
                                } else {
                                    let cnfl_lits = &cdb[ci].iter().copied().collect::<Vec<Lit>>();
                                    seen[0] = num_check;
                                    vec =
                                        asg.analyze_sandbox(cdb, &decisions, cnfl_lits, &mut seen);
                                    backtrack_sandbox(vars, asg, vam);
                                }
                            }
                            AssignReason::Decision(_) | AssignReason::None => {
                                unreachable!("vivify")
                            }
                        }
                        match vec.len() {
                            0 => {
                                state.flush("");
                                state[Stat::VivifiedClause] += num_shrink;
                                state[Stat::VivifiedVar] += num_assert;
                                state.log(None, "RootLevelConflict By vivify");
                                return Err(SolverError::EmptyClause);
                            }
                            1 => {
                                cdb.certificate_add_assertion(vec[0]);
                                assign_at_root_level(asg, vam, vec[0], &mut vars[vec[0].var.id])?;
                                num_assert += 1;
                            }
                            _ => {
                                #[cfg(feature = "clause_rewarding")]
                                if let Some(ci) = self.new_clause(asg, &mut vec, is_learnt).is_new()
                                {
                                    self.set_activity(ci, cp.value());
                                }
                                #[cfg(not(feature = "clause_rewarding"))]
                                cdb.new_clause(&mut vec, is_learnt);
                                cdb.remove_clause(cid);
                                num_shrink += 1;
                            }
                        }
                        continue 'next_clause;
                    }
                    //## Rule 4
                }
            }
        }
        if VIVIFY_LIMIT < num_check {
            break;
        }
    }
    backtrack_sandbox(vars, asg, vam);
    if asg.remains() {
        propagate_sandbox(vars, asg, vam, cdb).map_err(|_| SolverError::RootLevelConflict)?;
    }
    clear_asserted_literals(vars, asg, vam, cdb)?;
    debug_assert!(asg.stack_is_empty() || !asg.remains());
    state.flush("");
    state.flush(format!(
        "vivification(assert:{num_assert} shorten:{num_shrink}), "
    ));
    // state.log(
    //     asg.num_conflict,
    //     format!(
    //         "vivify:{:5}, pick:{:>8}, assert:{:>8}, shorten:{:>8}",
    //         state[Stat::Vivification],
    //         num_check,
    //         num_assert,
    //         num_shrink,
    //     ),
    // );
    state[Stat::VivifiedClause] += num_shrink;
    state[Stat::VivifiedVar] += num_assert;
    Ok(())
}

fn select_targets<'a>(
    asg: &mut AssignStack<'a>,
    cdb: &mut ClauseDB,
    initial_stage: bool,
    len: Option<usize>,
) -> Vec<OrderedProxy<ClauseId>> {
    if initial_stage {
        let mut seen: Vec<Option<OrderedProxy<ClauseId>>> = vec![None; 2 * (asg.num_vars + 1)];
        for (i, c) in cdb.iter().enumerate().skip(1) {
            if let Some(rank) = c.to_vivify(true) {
                let p = &mut seen[usize::from(c.lit0())];
                if p.as_ref().map_or(0.0, |r| r.value()) < rank {
                    *p = Some(OrderedProxy::new(ClauseId::from(i), rank));
                }
            }
        }
        let mut clauses = seen.iter().filter_map(|p| p.clone()).collect::<Vec<_>>();
        if let Some(max_len) = len {
            if 10 * max_len < clauses.len() {
                clauses.sort();
                clauses.truncate(max_len);
            }
        }
        clauses
    } else {
        let mut clauses: Vec<OrderedProxy<ClauseId>> = cdb
            .iter()
            .enumerate()
            .skip(1)
            .filter_map(|(i, c)| {
                c.to_vivify(false)
                    .map(|r| OrderedProxy::new_invert(ClauseId::from(i), r))
            })
            .collect::<Vec<_>>();
        if let Some(max_len) = len {
            if max_len < clauses.len() {
                clauses.sort();
                clauses.truncate(max_len);
            }
        }
        clauses
    }
}

impl<'a> AssignStack<'a> {
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
            seen[l.var.id] = key;
        }
        let last_decision = decisions.last().unwrap();
        let from = self.len_upto(self.root_level());
        let all = self.stack_iter().map(|l| !*l).collect::<Vec<_>>();
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
                .map(|l| l.var.reason)
                .collect::<Vec<_>>(),
            // am.iter().filter(|l| am.contains(&!**l)).collect::<Vec<_>>(),
        );
        // sweep in the reverse order
        for l in self.stack_iter().skip(self.len_upto(0)).rev() {
            if seen[l.var.id] != key {
                continue;
            }
            if decisions.contains(l) {
                // || assert!(!learnt.contains(l));
                // Quiz: which is the correct learnt clause here?
                // 1. [decision1, decision2, !last_decision]
                // 2. [!decision1, !decision2, !last_decision]
                // Since `conflict::conflict_analyze` sweeps *reason clauses*,
                // it collects positive literals out of the clauses in the dependency graph,
                // while we collect decision literals in *trail* here.
                // Thus we must negate the literals.
                learnt.push(!*l);
            }
            match l.var.reason {
                AssignReason::Decision(_) => (),
                AssignReason::BinaryLink(bil) => {
                    seen[bil.var.id] = key;
                }
                AssignReason::Implication(cid) => {
                    for r in cdb[cid].iter().skip(1) {
                        seen[r.var.id] = key;
                    }
                }
                AssignReason::None => unreachable!("analyze_sandbox::AssignReason::None"),
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
        // before finding a conflict by the target clause.
        // So we must skip this conflict.
        if learnt.is_empty() {
            debug_assert_eq!(self.num_conflict, 0);
            // panic!("\n{:?}\n{:?}\n{:?}",
            //        conflicting,
            //        conflicting.iter().map(|l| l.assigned()).collect::<Vec<_>>(),
            //        conflicting.iter().map(|l| l.val.level).collect::<Vec<_>>(),
            // );
            return learnt;
        }
        // make sure the decision var is at the top of list
        debug_assert!(
            !learnt.is_empty(),
            "empty learnt, conflict: {conflicting:?}, assumed: {decisions:?}"
        );
        debug_assert!(
            learnt.contains(&!*last_decision),
            "\nThe negation of the last decision {last_decision} isn't contained in {learnt:?}"
        );
        // Since we don't assign the right value of the 'reason' literal after conflict analysis,
        // we need not to swap locations.
        // learnt.swap(0, lst);
        // assert!(matches!(learnt[0].var.reason, AssignReason::None));
        debug_assert!(
            learnt.iter().all(|l| !learnt.contains(&!*l)),
            "res: {learnt:?} from: {decisions:?} and trail: {assumes:?}"
        );
        learnt
    }
}

impl<'a> Clause<'a> {
    /// return `true` if the clause should try vivification.
    /// smaller is better.
    #[cfg(feature = "clause_rewarding")]
    fn to_vivify(&self, initial_stage: bool) -> Option<f64> {
        if initial_stage {
            (!self.is_dead()).then(|| self.len() as f64)
        } else {
            (!self.is_dead()
                && self.rank * 2 <= self.rank_old
                && (self.is(FlagClause::LEARNT) || self.is(FlagClause::DERIVE20)))
            .then(|| self.reward)
        }
    }
    #[cfg(not(feature = "clause_rewarding"))]
    fn to_vivify(&self, initial_stage: bool) -> Option<f64> {
        if initial_stage {
            (!self.is_dead()).then(|| self.len() as f64)
        } else {
            (!self.is_dead()
                && self.rank * 2 <= self.rank_old
                && (self.is(FlagClause::LEARNT) || self.is(FlagClause::DERIVE20)))
            .then(|| -((self.rank_old - self.rank) as f64 / self.rank as f64))
        }
    }
    /// clear flags about vivification
    fn vivified(&mut self) {
        self.rank_old = self.rank;
        if !self.is(FlagClause::LEARNT) {
            self.turn_off(FlagClause::DERIVE20);
        }
    }
}

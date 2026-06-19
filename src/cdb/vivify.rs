//! Vivification
#![allow(dead_code)]
use crate::{
    assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
    cdb::{ClauseDB, ClauseDBIF, clause::ClauseIF},
    state::{Stat, State, StateIF},
    types::*,
};

pub trait VivifyIF {
    fn vivify(
        &mut self,
        asg: &mut AssignStack,
        state: &mut State,
        skip_evaluation: bool,
    ) -> MaybeInconsistent;
}

impl VivifyIF for ClauseDB {
    /// vivify clauses under `asg`
    fn vivify(
        &mut self,
        asg: &mut AssignStack,
        state: &mut State,
        eval: bool,
    ) -> MaybeInconsistent {
        // This is a reusable vector to reduce memory consumption,
        // the key is the number of invocation
        let mut seen: Vec<usize> = vec![0; asg.num_vars + 1];
        let display_step: usize = 1000;
        let mut num_check = 0;
        let mut num_shrink = 0;
        let mut num_assert = 0;
        let mut to_display = 0;
        state[Stat::Vivification] += 1;
        if eval && asg.remains() {
            asg.propagate_sandbox(self).map_err(|cc| {
                state.log(None, "By vivifier");
                SolverError::RootLevelConflict(cc)
            })?;
        }
        // Inlined target selection (formerly `select_targets`).
        // Pick clauses that haven't been vivified recently. We deliberately
        // do NOT sort the candidates: the per-clause filter in the loop below
        // decides which ones are actually worth processing.
        'next_clause: for i in 1..self.clause.len() {
            let cid = ClauseId::from(i);
            let c = &mut self[cid];
            if c.is_dead() {
                continue;
            }
            if c.referred_at + 20_000 * (1 + c.vivify_age) > asg.num_conflict {
                continue;
            }
            let c = &mut self[cid];
            c.vivified();
            // Skip clauses that are unlikely to be improved by vivification.
            // Empirically success concentrates on clauses
            // that are not too short and have a moderate LBD; outside this band
            // the success rate collapses, so skipping them saves work without
            // losing many improvable clauses.
            if !eval
                || c.vivify_age >= 6
                || c.len() < 9_usize.saturating_sub(c.vivify_age)
                || 12 < asg.literal_block_distance_current(&c.lits)
            {
                continue;
            }
            let is_learnt = c.is(FlagClause::LEARNT);
            let vivify_age = c.vivify_age;
            let referred_at = c.referred_at;
            let reference_rate = c.reference_rate;
            let clits = c.iter().copied().collect::<Vec<Lit>>();
            if to_display <= num_check {
                state.flush("");
                state.flush(format!(
                    "clause vivifying(assert:{num_assert} shorten:{num_shrink}, check:{num_check})..."
                ));
                to_display = num_check + display_step;
            }
            num_check += 1;
            // debug_assert!(clits.iter().all(|l| !clits.contains(&!*l)));
            // Build a clean environment
            // debug_assert!(asg.stack_is_empty() || !asg.remains());
            // debug_assert_eq!(asg.root_level(), asg.decision_level());
            asg.backtrack_sandbox();
            debug_assert_eq!(asg.decision_level(), asg.root_level());
            if asg.remains() {
                asg.propagate_sandbox(self)
                    .map_err(SolverError::RootLevelConflict)?;
            }
            let mut decisions: Vec<Lit> = Vec::new();
            for lit in clits.iter().copied() {
                // assert!(!asg.var(lit.vi()).is(FlagVar::ELIMINATED));
                match asg.assigned(!lit) {
                    //## Rule 1
                    Some(false) => (),
                    //## Rule 2
                    Some(true) => break,
                    None => {
                        decisions.push(!lit);
                        asg.assign_by_decision(!lit);
                        //## Rule 3
                        if let Err(cc) = asg.propagate_sandbox(self) {
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
                                        asg.backtrack_sandbox();
                                        continue 'next_clause;
                                    } else {
                                        // debug_assert!(clits.len() != 2 || decisions.len() != 2);
                                        seen[0] = num_check;
                                        vec = asg.analyze_sandbox(
                                            self, &decisions, &cnfl_lits, &mut seen,
                                        );
                                        asg.backtrack_sandbox();
                                    }
                                }
                                AssignReason::Implication(ci) => {
                                    if ci == cid && clits.len() == decisions.len() {
                                        asg.backtrack_sandbox();
                                        continue 'next_clause;
                                    } else {
                                        let cnfl_lits =
                                            &self[ci].iter().copied().collect::<Vec<Lit>>();
                                        seen[0] = num_check;
                                        vec = asg.analyze_sandbox(
                                            self, &decisions, cnfl_lits, &mut seen,
                                        );
                                        asg.backtrack_sandbox();
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
                                    self.certificate_add_assertion(vec[0]);
                                    asg.assign_at_root_level(self, vec[0])?;
                                    num_assert += 1;
                                }
                                _ => {
                                    if let Some(cid) = self.new_clause(&mut vec, is_learnt).is_new()
                                    {
                                        self[cid].referred_at = referred_at;
                                        self[cid].reference_rate = reference_rate;
                                        self[cid].vivify_age = vivify_age;
                                    }
                                    self.remove_clause(cid);
                                    num_shrink += 1;
                                }
                            }
                            continue 'next_clause;
                        }
                        //## Rule 4
                    }
                }
            }
        }
        if !eval {
            return Ok(());
        }
        asg.backtrack_sandbox();
        if asg.remains() {
            asg.propagate_sandbox(self)
                .map_err(SolverError::RootLevelConflict)?;
        }
        asg.clear_asserted_literals(self)?;
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
            match self.reason(l.vi()) {
                AssignReason::Decision(_) => (),
                AssignReason::BinaryLink(bil) => {
                    seen[bil.vi()] = key;
                }
                AssignReason::Implication(cid) => {
                    for r in cdb[cid].iter().skip(1) {
                        seen[r.vi()] = key;
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
            //        conflicting.iter().map(|l| self.assigned(*l)).collect::<Vec<_>>(),
            //        conflicting.iter().map(|l| self.level(l.vi())).collect::<Vec<_>>(),
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
        // assert!(matches!(self.reason(learnt[0].vi()), AssignReason::None));
        debug_assert!(
            learnt.iter().all(|l| !learnt.contains(&!*l)),
            "res: {learnt:?} from: {decisions:?} and trail: {assumes:?}"
        );
        learnt
    }
}

impl Clause {
    /// clear flags about vivification
    fn vivified(&mut self) {
        self.vivify_age += 1;
        self.reference_rate *= 0.8;
        self.reference_rate += 0.2 * self.referred as f64;
        self.referred = 0;
    }
}

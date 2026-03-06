/// Implementation of Stochastic Local Search
use {
    super::{Clause, ClauseDB, VarId},
    crate::{assign::AssignIF, types::*},
    std::collections::HashMap,
};

pub trait StochasticLocalSearchIF {
    /// returns the decision level of the given assignment and the one of the final assignment.
    /// Note: the lower level a set of clauses make a conflict at,
    /// the higher learning rate a solver can keep and the better learnt clauses we will have.
    /// This would be a better criteria that can be used in CDCL solvers.
    fn stochastic_local_search(
        &mut self,
        asg: &impl AssignIF,
        start: &mut HashMap<VarId, bool>,
        limit: usize,
    ) -> (usize, usize);
}

impl StochasticLocalSearchIF for ClauseDB {
    fn stochastic_local_search(
        &mut self,
        _asg: &impl AssignIF,
        assignment: &mut HashMap<VarId, bool>,
        limit: usize,
    ) -> (usize, usize) {
        let mut returns: (usize, usize) = (0, 0);
        let mut last_flip = self.num_clause;
        let mut seed = 721_109;
        for step in 1..=limit {
            let mut unsat_clauses = 0;
            // let mut level: DecisionLevel = 0;
            // CONSIDER: counting only given (permanent) clauses.
            let mut flip_target: HashMap<VarId, usize> = HashMap::new();
            let mut target_clause: Option<&Clause> = None;
            for c in self.clause.iter().skip(1).filter(|c| !c.is_dead()) {
                // let mut cls_lvl: DecisionLevel = 0;
                if c.is_falsified(assignment, &mut flip_target) {
                    unsat_clauses += 1;
                    // for l in c.lits.iter() {
                    //     cls_lvl = cls_lvl.max(asg.level(l.vi()));
                    // }
                    // level = level.max(cls_lvl);
                    if target_clause.is_none() || unsat_clauses == step {
                        target_clause = Some(c);
                        for l in c.lits.iter() {
                            flip_target.entry(l.vi()).or_insert(0);
                        }
                    }
                }
            }
            if step == 1 {
                returns.0 = unsat_clauses;
                // returns.0 = level as usize;
            }
            returns.1 = unsat_clauses;
            // returns.1 = level as usize;
            if unsat_clauses == 0 || step == limit {
                break;
            }
            seed = ((((!seed & 0x0000_0000_ffff_ffff) * 1_304_003) % 2_003_819)
                ^ ((!last_flip & 0x0000_0000_ffff_ffff) * seed))
                % 3_754_873;
            if let Some(c) = target_clause {
                let beta: f64 = 3.2 - 2.1 / (1.0 + unsat_clauses as f64).log(2.0);
                // let beta: f64 = if unsat_clauses <= 3 { 1.0 } else { 3.0 };
                let factor = |vi| beta.powf(-(*flip_target.get(vi).unwrap() as f64));
                let vars = c.lits.iter().map(|l| l.vi()).collect::<Vec<_>>();
                let index = ((seed % 100) as f64 / 100.0) * vars.iter().map(factor).sum::<f64>();
                let mut sum: f64 = 0.0;
                for vi in vars.iter() {
                    sum += factor(vi);
                    if index <= sum {
                        assignment.entry(*vi).and_modify(|e| *e = !*e);
                        last_flip = *vi;
                        break;
                    }
                }
            } else {
                break;
            }
        }
        returns
    }
}

impl Clause {
    fn is_falsified(
        &self,
        assignment: &HashMap<VarId, bool>,
        flip_target: &mut HashMap<VarId, usize>,
    ) -> bool {
        let mut num_sat = 0;
        let mut sat_vi = 0;
        for l in self.iter() {
            let vi = l.vi();
            match assignment.get(&vi) {
                Some(b) if *b == l.as_bool() => {
                    if num_sat == 1 {
                        return false;
                    }
                    num_sat += 1;
                    sat_vi = vi;
                }
                None => unreachable!(),
                _ => (),
            }
        }
        if num_sat == 0 {
            true
        } else {
            *flip_target.entry(sat_vi).or_insert(0) += 1;
            false
        }
    }
}

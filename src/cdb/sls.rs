/// Implementation of Stochastic Local Search
use {crate::types::*, std::collections::HashMap};

pub trait StochasticLocalSearchIF {
    fn stochastic_local_search(
        &mut self,
        start: &mut HashMap<VarId, bool>,
        limit: usize,
    ) -> (usize, usize);
}

impl StochasticLocalSearchIF for ClauseDB {
    fn stochastic_local_search(
        &mut self,
        assignment: &mut HashMap<VarId, bool>,
        limit: usize,
    ) -> (usize, usize) {
        let mut returns = (0, 0);
        let mut last_flip = 0;
        for step in 0..limit {
            let mut unsat_clauses = 0;
            let mut flip_target: HashMap<VarId, usize> = HashMap::new();
            let mut target_clause: Option<&Clause> = None;
            for c in self
                .clause
                .iter()
                .skip(1)
                .rev()
                .filter(|c| /* !c.is(FlagClause::LEARNT) && */ !c.is_dead())
            {
                let result = c.check_parity(assignment, &mut flip_target);
                if let Some(c) = result {
                    unsat_clauses += 1;
                    if target_clause.is_none() || unsat_clauses == step {
                        target_clause = result;
                        for l in c.lits.iter() {
                            flip_target.entry(l.vi()).or_insert(0);
                        }
                    }
                }
            }
            if step == 1 {
                returns = (unsat_clauses, unsat_clauses);
            }
            returns.1 = unsat_clauses;
            if let Some(c) = target_clause {
                let factor = |vi| 3.2_f64.powf(-(*flip_target.get(vi).unwrap() as f64));
                let vars = c.lits.iter().map(|l| l.vi()).collect::<Vec<_>>();
                let index = (((step + last_flip) & 63) as f64 / 63.0)
                    * vars.iter().map(factor).sum::<f64>();
                let mut sum: f64 = 0.0;
                for vi in vars.iter() {
                    sum += factor(vi);
                    if index <= sum {
                        // print!(
                        //     "step {step}: flip {} of {}| {}",
                        //     vi,
                        //     c.lits.len(),
                        //     assignment[vi]
                        // );
                        assignment.entry(*vi).and_modify(|e| *e = !*e);
                        last_flip = *vi;
                        break;
                    }
                }
            } else {
                return returns;
            }
        }
        returns
    }
}

impl Clause {
    fn check_parity(
        &self,
        assignment: &HashMap<VarId, bool>,
        flip_target: &mut HashMap<VarId, usize>,
    ) -> Option<&Self> {
        let mut num_sat = 0;
        let mut sat_vi = 0;
        for l in self.iter() {
            let vi = l.vi();
            match assignment.get(&vi) {
                Some(b) if *b == l.as_bool() => {
                    num_sat += 1;
                    sat_vi = vi;
                }
                None => unreachable!(),
                _ => (),
            }
        }
        if num_sat == 1 {
            *flip_target.entry(sat_vi).or_insert(0) += 1;
        }
        (0 == num_sat).then_some(self)
    }
}

/// Implementation of Stochastic Local Search
use {crate::types::*, std::collections::HashMap};

pub trait StochasticLocalSearchIF {
    fn stochastic_local_search(&mut self, start: &[Option<bool>], limit: usize) -> Vec<bool>;
}

impl StochasticLocalSearchIF for ClauseDB {
    fn stochastic_local_search(&mut self, start: &[Option<bool>], limit: usize) -> Vec<bool> {
        let mut assignment: Vec<bool> = start
            .iter()
            .map(|a| a.map_or(false, |b| b))
            .collect::<Vec<_>>();
        for _ in 0..limit {
            let mut flip_target: HashMap<VarId, usize> = HashMap::new();
            let mut satisfied = true;
            for c in self
                .clause
                .iter()
                .skip(1)
                .filter(|c| !c.is(FlagClause::LEARNT))
            {
                satisfied &= c.check_parity(&assignment, &mut flip_target);
            }
            if satisfied {
                return assignment;
            }
            let i: usize = flip_target.iter().map(|(k, v)| (*v, *k)).max().unwrap().1;
            assignment[i] = !assignment[i];
        }
        assignment
    }
}

impl Clause {
    fn check_parity(&self, assignment: &[bool], flip_target: &mut HashMap<VarId, usize>) -> bool {
        for l in self.iter() {
            let vi = l.vi();
            if assignment[vi] != l.as_bool() {
                *flip_target.entry(vi).or_insert(0) += 1;
            }
        }
        todo!();
    }
}

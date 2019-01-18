use crate::solver::Solver;
use crate::traits::{LitIF, ValidatorIF, VarDBIF};
use crate::types::Lbool;

impl ValidatorIF for Solver {
    fn inject_assigmnent(&mut self, vec: &[i32]) {
        for val in vec {
            self.vars[val.abs() as usize].assign = (0 < *val) as Lbool;
        }
    }
    /// returns None if the given assignment is a model of a problem.
    /// Otherwise returns a clause which is not satisfiable under a given assignment.
    fn validate(&self) -> Option<Vec<i32>> {
        for ch in &self.cdb.clause[1..] {
            if !self.vars.satisfies(&ch.lits) {
                let mut v = Vec::new();
                for l in &ch.lits {
                    v.push(l.int());
                }
                return Some(v);
            }
        }
        None
    }
}

use crate::solver::Solver;
use crate::traits::{LitIF, PropagatorIF, ValidatorIF, VarDBIF};
use crate::types::{Lit, MaybeInconsistent, SolverError, NULL_CLAUSE};

impl ValidatorIF for Solver {
    fn inject_assigmnent(&mut self, vec: &[i32]) -> MaybeInconsistent {
        if vec.is_empty() {
            return Err(SolverError::Inconsistent);
        }
        for val in vec {
            let l = Lit::from_int(*val);
            let vi = l.vi();
            self.asgs
                .enqueue(&mut self.vdb[vi], l.as_bool(), NULL_CLAUSE, 0)?;
        }
        Ok(())
    }
    /// returns None if the given assignment is a model of a problem.
    /// Otherwise returns a clause which is not satisfiable under a given assignment.
    fn validate(&self) -> Option<Vec<i32>> {
        for ch in &self.cdb[1..] {
            if !self.vdb.satisfies(&ch.lits) {
                let mut v = Vec::new();
                for l in &ch.lits {
                    v.push(l.to_i32());
                }
                return Some(v);
            }
        }
        None
    }
}

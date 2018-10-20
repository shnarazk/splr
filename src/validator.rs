use clause::CLAUSE_KINDS;
use solver::*;
use types::*;
use var::Satisfiability;

impl Solver {
    pub fn inject_assigmnent(&mut self, vec: &[i32]) -> () {
        for val in vec {
            self.vars[val.abs() as usize].assign = if *val < 0 { LFALSE } else { LTRUE };
        }
    }

    /// returns None if the given assignment is a model of a problem.
    /// Otherwise returns a clause which is not satisfiable.
    pub fn validate(&self) -> Option<Vec<i32>> {
        for ck in &CLAUSE_KINDS {
            for ci in 1..self.cp[*ck as usize].head.len() {
                let cb = &self.cp[*ck as usize].body[ci];
                if !self.vars.satisfies(&cb.lits) {
                    let mut v = Vec::new();
                    for l in &cb.lits {
                        v.push(l.int());
                    }
                    return Some(v);
                }
            }
        }
        None
    }
}

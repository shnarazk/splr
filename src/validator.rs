use types::*;
use solver::*;
use clause_manage::KINDS;

impl Solver {
    pub fn inject_assigmnent(&mut self, vec: &Vec<i32>) -> () {
        for val in vec {
            self.vars[val.abs() as usize].assign = if *val < 0 { LFALSE } else { LTRUE };
        }
    }
    pub fn validate(&self) -> bool {
        for ck in &KINDS {
            for c in &self.cp[*ck as usize].clauses[1..] {
                if !self.satisfies(&c) {
                    return false;
                }
            }
        }
        true
    }
}

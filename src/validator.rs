use types::*;
use solver::*;
use clause_manage::KINDS;
use var::Satisfiability;

impl Solver {
    pub fn inject_assigmnent(&mut self, vec: &Vec<i32>) -> () {
        for val in vec {
            self.vars[val.abs() as usize].assign = if *val < 0 { LFALSE } else { LTRUE };
        }
    }
    pub fn validate(&self) -> Option<Vec<i32>> {
        for ck in &KINDS {
            for c in &self.cp[*ck as usize].clauses[1..] {
                if !(&self.vars[..]).satisfies(&c) {
                    let mut v = Vec::new();
                    for i in 0..c.len() {
                        let l = lindex!(c, i);
                        v.push(l.int());
                    }
                    return Some(v);
                }
            }
        }
        None
    }
}

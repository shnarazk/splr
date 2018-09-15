use types::*;
use solver::*;
use clause::CLAUSE_KINDS;
use var::Satisfiability;

impl Solver {
    pub fn inject_assigmnent(&mut self, vec: &[i32]) -> () {
        for val in vec {
            self.assign[val.abs() as usize] = if *val < 0 { LFALSE } else { LTRUE };
        }
    }
    pub fn validate(&self) -> Option<Vec<i32>> {
        for ck in &CLAUSE_KINDS {
            for c in &self.cp[*ck as usize].clauses[1..] {
                if !(&self.assign[..]).satisfies(&c) {
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

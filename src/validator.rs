use crate::clause::ClauseKind;
use crate::solver::*;
use crate::types::*;
use crate::var::Satisfiability;

impl Solver {
    pub fn inject_assigmnent(&mut self, vec: &[i32]) -> () {
        for val in vec {
            self.vars[val.abs() as usize].assign = if *val < 0 { LFALSE } else { LTRUE };
        }
    }

    /// returns None if the given assignment is a model of a problem.
    /// Otherwise returns a clause which is not satisfiable.
    pub fn validate(&self) -> Option<Vec<i32>> {
        for ck in ClauseKind::Liftedlit as usize ..= ClauseKind::Binclause as usize {
            for ci in 1..self.cp[ck].head.len() {
                let ch = &self.cp[ck].head[ci];
                if !self.vars.satisfies(&ch.lits) {
                    let mut v = Vec::new();
                    for l in &ch.lits {
                        v.push(l.int());
                    }
                    return Some(v);
                }
            }
        }
        None
    }
}

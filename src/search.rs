#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use clause::*;
use solver::*;
use types::*;

impl Solver {
    pub fn rebuild_reason(&self, permutation: &Vec<ClauseIndex>) -> () {}
    pub fn solve(&mut self) -> () {
        propagate(self, 0);
    }
}

fn search(_s: &mut Solver) -> () {}

fn propagate(_s: &mut Solver, _l: Lit) -> Option<&Clause> {
    None
}

fn analyze(_s: &mut Solver, _l: Lit) -> (u32, Clause) {
    (0, Clause::new(vec![]))
}

fn simplify(_s: &mut Solver) -> () {}

fn reduce(_s: &mut Solver) -> () {}

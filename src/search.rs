#![allow(dead_code)]
#![allow(unused_imports)]
use clause::*;
use solver::*;
use types::*;

impl<'a> Solver<'a> {
    pub fn solve(&mut self) -> () {
        propagate(self, 0);
    }
}

fn search(_s: &mut Solver) -> () {}

fn propagate<'a>(_s: &'a mut Solver, _l: Lit) -> Option<&'a Clause> {
    None
}

fn analyze(_s: &mut Solver, _l: Lit) -> (u32, Clause) {
    (0, Clause::new(vec![]))
}

fn simplify(_s: &mut Solver) -> () {}

fn reduce(_s: &mut Solver) -> () {}

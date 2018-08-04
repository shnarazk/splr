#![allow(dead_code)]
#![allow(unused_imports)]
use clause::*;
use solver::*;
use types::*;

impl<'a> Solver<'a> {
    pub fn solve(&mut self) -> () {
        propagate(self, 0);
    }
    pub fn search(&self) -> () {}
}

fn propagate(_s: &mut Solver, _l: Lit) -> () {}

fn analyze(_s: &mut Solver, _l: Lit) -> () {}

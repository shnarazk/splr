#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use clause::*;
use solver::*;
use types::*;

impl Solver {
    /// # Note on database reduction
    /// 1. sort_clause(&mut self) -> perm: Vec<ClauseIndex>
    /// 2. rebuild_reason(&mut self, perm: Vec<ClauseIndex>) -> ()
    /// 3. rebuild_watches(&mut self) -> ()
    fn rebuild_reason(&mut self, perm: &Vec<ClauseIndex>) -> () {
        for i in 1..self.vars.len() + 1 {
            let v = &mut self.vars[i];
            let ci = v.reason;
            if 0 < ci {
                v.reason = perm[ci as usize];
            }
        }
    }
    fn rebuild_watches(&mut self) -> () {
        // Firstly, clear everything.
        for i in 1..self.watches.len() + 1 {
            let w = &mut self.watches[i];
            w.clear();
        }
        for c in &self.clauses {
            register_to_watches(&mut self.watches, c.index, c.lits[0], c.lits[1]);
        }
        for c in &self.learnts {
            register_to_watches(&mut self.watches, c.index, c.lits[0], c.lits[1]);
        }
    }
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

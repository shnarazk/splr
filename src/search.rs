#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use clause::*;
use solver::*;
use std::cmp::max;
use types::*;

impl Solver {
    pub fn reduce_database(&mut self) -> () {
        let keep = self.sort_learnts();
        self.rebuild_reason();
        self.rebuild_watches(); // O(n)?
                                // self.check_clause_index_consistency();
        self.learnts.truncate(keep);
    }
    // Note: this function changes self.learnt_permutation.
    fn sort_learnts(&mut self) -> usize {
        let nc = self.learnts.len();
        let mut requires = 0;
        for c in &self.learnts {
            requires += c.set_sort_key();
        }
        self.learnts.sort_by_key(|c| c.key);
        for i in 1..nc {
            let old = self.learnts[i].index as usize;
            self.learnt_permutation[old] = i as ClauseIndex;
        }
        max(requires, nc / 2)
    }
    fn rebuild_reason(&mut self) -> () {
        let perm = &self.learnt_permutation;
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
    fn propagate(&mut self, _l: Lit) -> Option<&Clause> {
        None
    }
    fn search(&mut self) -> () {}
    pub fn solve(&mut self) -> () {
        self.propagate(0);
    }
}

fn analyze(_s: &mut Solver, _l: Lit) -> (u32, Clause) {
    (0, Clause::new(vec![]))
}

fn simplify(_s: &mut Solver) -> () {}

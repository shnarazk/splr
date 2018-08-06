#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use clause::*;
use solver::*;
use std::cmp::max;
use types::*;

impl Solver {
    /// renamed from newLearntClause
    pub fn new_learnt(&mut self, v: Vec<Lit>) -> usize {
        let k = v.len();
        if k == 0 {
            self.unsafe_enqueue(v[0], NULL_CLAUSE);
            return 1;
        }
        let mut c = Clause::new(v);
        let mut j = 0;
        let mut lvm = 0; // level max
                         // seek a literal with max level
        for i in 0..c.lits.len() {
            let vi = c.lits[i].vi();
            let lv = self.vars[vi].level;
            if self.vars[vi].assign != BOTTOM && lvm < lv {
                j = i;
                lvm = lv;
            }
        }
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        let lj = c.lits[j];
        let lbd = self.lbd_of(&c.lits);
        c.rank = lbd;
        c.lits[j] = l1;
        c.lits[1] = lj;
        let ci = self.inject(true, c);
        self.bump_ci(ci);
        self.unsafe_enqueue(l0, ci);
        lbd
    }
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
    fn unsafe_enqueue(&mut self, l: Lit, ci: ClauseIndex) -> () {}
}

fn analyze(_s: &mut Solver, _l: Lit) -> (u32, Clause) {
    (0, Clause::new(vec![]))
}

fn simplify(_s: &mut Solver) -> () {}

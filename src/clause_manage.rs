use clause::*;
use search::SolveSAT;
use solver::*;
use std::cmp::max;
use std::cmp::min;
use std::usize::MAX;
use types::*;
use watch::set_watch;

const CLAUSE_ACTIVITY_THRESHOLD: f64 = 1e20;

pub trait ClauseManagement {
    fn bump_ci(&mut self, ci: ClauseIndex) -> ();
    fn decay_cla_activity(&mut self) -> ();
    fn add_clause(&mut self, v: Vec<Lit>) -> bool;
    fn add_learnt(&mut self, v: Vec<Lit>) -> usize;
    fn reduce_database(&mut self) -> ();
    fn simplify_database(&mut self) -> ();
}

impl ClauseManagement for Solver {
    fn bump_ci(&mut self, ci: ClauseIndex) -> () {
        if ci <= 0 {
            return;
        }
        let a = self.clauses[ci].activity + self.cla_inc;
        self.clauses[ci].activity = a;
        if CLAUSE_ACTIVITY_THRESHOLD < a {
            self.rescale_clause_activity()
        }
    }
    fn decay_cla_activity(&mut self) -> () {
        self.cla_inc = self.cla_inc / self.config.clause_decay_rate;
    }
    // renamed from clause_new
    fn add_clause(&mut self, mut v: Vec<Lit>) -> bool {
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means totology.
        for i in 0..v.len() {
            let li = v[i];
            let sat = self.assigned(li);
            if sat == LTRUE || li.negate() == l_ {
                return true;
            } else if sat != LFALSE && li != l_ {
                v[j] = li;
                j += 1;
                l_ = li;
            }
        }
        v.truncate(j);
        match v.len() {
            0 => true,
            1 => self.enqueue(v[0], NULL_CLAUSE),
            _ => {
                self.attach_clause(Clause::new(RANK_CONST, v));
                true
            }
        }
    }
    /// renamed from newLearntClause
    fn add_learnt(&mut self, v: Vec<Lit>) -> usize {
        let lbd;
        if v.len() == 2 {
            lbd = RANK_NEED;
        } else {
            lbd = self.lbd_of(&v);
        }
        let mut c = Clause::new(lbd, v);
        let mut i_max = 0;
        let mut lv_max = 0;
        // seek a literal with max level
        for i in 0..c.lits.len() {
            let vi = c.lits[i].vi();
            let lv = self.vars[vi].level;
            if self.vars[vi].assign != BOTTOM && lv_max < lv {
                i_max = i;
                lv_max = lv;
            }
        }
        c.lits.swap(1, i_max);
        let l0 = c.lits[0];
        let ci = self.attach_clause(c);
        self.bump_ci(ci);
        self.uncheck_enqueue(l0, ci);
        lbd
    }
    fn reduce_database(&mut self) -> () {
        let end = self.clauses.len();
        let start = self.fixed_len;
        debug_assert_ne!(start, 0);
        let nc = self.clauses.len();
        if self.clause_permutation.len() < nc {
            unsafe {
                self.clause_permutation.reserve(nc + 1);
                self.clause_permutation.set_len(nc + 1);
            }
        }
        // reinitialize the permutation table.
        for (i, x) in self.clause_permutation.iter_mut().enumerate() {
            *x = i;
        }
        // mark clauses that used as reasons
        for v in &self.vars[1..] {
            if 0 < v.reason {
                self.clauses[v.reason].tmp = RANK_NEED;
            }
        }
        // set key
        let ac = 0.1 * self.cla_inc / (nc as f64);
        let mut requires = 0;
        let mut npurge = 0;
        for ci in start..self.clauses.len() {
            let ref mut c = &mut self.clauses[ci];
            debug_assert_ne!(c.rank, RANK_NULL);
            debug_assert_ne!(c.rank, RANK_CONST);
            if c.tmp == RANK_NEED {
                requires += 1;
            } else if c.rank <= RANK_NEED {
                c.tmp = c.rank;
                requires += 1;
            } else if c.activity < ac {
                c.tmp = MAX;
                npurge += 1;
            } else {
                c.tmp = c.rank;
            }
        }
        let new_end = start + max(requires, min((nc - start) / 2, nc - start - npurge));
        // sort the range
        self.clauses[start..].sort();
        // update permutation table.
        for i in 1..new_end {
            let old = self.clauses[i].index;
            debug_assert_ne!(old, 0);
            self.clause_permutation[old] = i;
            self.clauses[i].index = i;
        }
        // DEBUG: check consistency
        // {
        //     let mut r0 = 0;
        //     let mut r1 = 0;
        //     for c in &self.clauses[start..start + requires] {
        //         match c.tmp {
        //             RANK_NEED => { r0 += 1; }
        //             _ => { break; }
        //         }
        //     }
        //     for c in &self.clauses[start..start + requires] {
        //         match c.tmp {
        //             RANK_NEED => { r1 += 1; }
        //             _ => {}
        //         }
        //     }
        //     debug_assert_eq!(r0, r1);
        //     debug_assert_eq!(r0, requires);
        //     debug_assert!(self.clauses[0].index == 0, "NULL moved.");
        //     debug_assert_eq!(start + r0, self.fixed_len + requires);
        // }
        self.fixed_len += requires;
        // END
        if new_end == end {
            return;
        }
        self.clauses.truncate(new_end);
        // rebuild reason
        for v in &mut self.vars[1..] {
            let ci = v.reason;
            if 0 < ci {
                v.reason = self.clause_permutation[ci];
            }
        }
        // rebuild watches
        for w in &mut self.watches {
            w.clear();
        }
        debug_assert_eq!(self.clauses[0].index, 0);
        for c in &self.clauses[1..] {
            if 2 <= c.lits.len() {
                set_watch(&mut self.watches, c.index, c.lits[0], c.lits[1]);
            }
        }
        println!(
            "# DB::drop 1/2 {:>9} ({:>9}) => {:>9} / {:>9.1}",
            end, self.fixed_len, new_end, self.max_learnts
        );
    }
    fn simplify_database(&mut self) -> () {
        debug_assert_eq!(self.decision_level(), 0);
        let end = self.clauses.len();
        // remove clauses containing new fixed literals
        let targets: Vec<Lit> = self.trail[self.num_solved_vars..]
            .iter()
            .map(|l| l.negate())
            .collect();
        for mut c in &mut self.clauses {
            c.lits.retain(|l| {
                for t in &targets {
                    if t == l {
                        return false;
                    }
                }
                true
            });
        }
        let nc = self.clauses.len();
        let mut purges = 0;
        if self.clause_permutation.len() < nc {
            unsafe {
                self.clause_permutation.reserve(nc + 1);
                self.clause_permutation.set_len(nc + 1);
            }
        }
        // reinitialize the permutation table.
        for x in &mut self.clause_permutation {
            *x = 0;
        }
        // set key
        for ci in 1..self.clauses.len() {
            unsafe {
                let c = &mut self.clauses[ci] as *mut Clause;
                if self.satisfies(&self.clauses[ci]) {
                    (*c).tmp = MAX;
                    purges += 1;
                } else if (*c).lits.len() == 1 {
                    if !self.enqueue((*c).lits[0], NULL_CLAUSE) {
                        self.ok = false;
                    }
                    (*c).tmp = MAX;
                } else {
                    if RANK_NEED < (*c).rank {
                        let new = self.lbd_of(&(*c).lits);
                        if new < (*c).rank {
                            (*c).rank = new;
                        }
                    }
                    (*c).tmp = 0;
                }
            }
        }
        self.clauses.retain(|ref c| c.tmp < MAX);
        let new_end = self.clauses.len();
        debug_assert_eq!(new_end, nc - purges);
        for i in 1..new_end {
            let old = self.clauses[i].index;
            debug_assert!(0 < old, "0 index");
            self.clause_permutation[old] = i;
            self.clauses[i].index = i;
        }
        // clear the reasons of variables satisfied at level zero.
        for l in &self.trail {
            self.vars[l.vi() as usize].reason = NULL_CLAUSE;
        }
        let mut c0 = 0;
        for c in &self.clauses[..] {
            if c.rank <= RANK_NEED {
                c0 += 1;
            } else {
                break;
            }
        }
        if new_end == end {
            return;
        }
        self.fixed_len = c0;
        self.clauses.truncate(new_end);
        // rebuild watches
        let (w0, wr) = self.watches.split_first_mut().unwrap();
        w0.clear();
        for ws in wr {
            while let Some(mut w) = ws.pop() {
                match self.clause_permutation[w.by] {
                    0 => {}
                    x => {
                        w.by = x;
                        w0.push(w);
                    }
                }
            }
            while let Some(w) = w0.pop() {
                ws.push(w);
            }
        }
        println!(
            "# DB::simplify {:>9} ({:>9}) => {:>9} / {:>9.1}",
            end, self.fixed_len, new_end, self.max_learnts
        );
    }
}

impl Solver {
    pub fn lbd_of(&mut self, v: &[Lit]) -> usize {
        if v.len() == 2 {
            return RANK_NEED;
        }
        let k = 1 + self.lbd_key;
        self.lbd_key = k;
        if 1000_000 < k {
            self.lbd_key = 0;
        }
        let mut cnt = 0;
        for l in v {
            let lv = self.vars[l.vi()].level;
            if self.lbd_seen[lv] != k && lv != 0 {
                self.lbd_seen[lv] = k;
                cnt += 1;
            }
        }
        RANK_NEED + 1 + cnt
    }
    fn rescale_clause_activity(&mut self) -> () {
        for i in self.fixed_len..self.clauses.len() {
            self.clauses[i].activity = self.clauses[i].activity / CLAUSE_ACTIVITY_THRESHOLD;
        }
        self.cla_inc /= CLAUSE_ACTIVITY_THRESHOLD;
    }
}

use clause::*;
use solver::*;
use std::cmp::max;
use std::cmp::min;
use std::usize::MAX;
use types::*;
use watch::push_watch;

// const RANK_WIDTH: u64 = 11;
const ACTIVITY_WIDTH: usize = 51;
const RANK_MAX: usize = 1000;
const ACTIVITY_MAX: usize = 2 ^ ACTIVITY_WIDTH - 1;
const CLAUSE_ACTIVITY_THRESHOLD: f64 = 1e20;

fn scale_activity(x: f64) -> usize {
    if x < 1e-20 {
        ACTIVITY_MAX
    } else {
        (ACTIVITY_MAX * ((1.0 - (x * 1e20).log10() / 40.0) as usize))
    }
}

/// returns 1 if this is good enough.
impl Clause {
    pub fn set_sort_key(&mut self, at: f64) -> usize {
        if self.rank == 0 {
            // only NULL and given
            self.tmp = 0;
            1
        } else if self.rank == 1 {
            self.tmp = 1;
            1
        } else {
            let ac = self.activity;
            let d = if ac < at {
                RANK_MAX // bigger is worse
            } else {
                min(RANK_MAX, self.rank)
            };
            self.tmp = (d << ACTIVITY_WIDTH) + scale_activity(ac);
            0
        }
    }
}

impl Solver {
    pub fn bump_ci(&mut self, ci: ClauseIndex) -> () {
        if ci <= 0 {
            return;
        }
        let a = self.clauses[ci].activity + self.cla_inc;
        self.clauses[ci].activity = a;
        if CLAUSE_ACTIVITY_THRESHOLD < a {
            self.rescale_clause_activity()
        }
    }
    pub fn decay_cla_activity(&mut self) -> () {
        self.cla_inc = self.cla_inc / CLAUSE_ACTIVITY_THRESHOLD;
    }
    pub fn rescale_clause_activity(&mut self) -> () {
        for i in self.fixed_len..self.clauses.len() {
            self.clauses[i].activity = self.clauses[i].activity / CLAUSE_ACTIVITY_THRESHOLD;
        }
        self.cla_inc /= CLAUSE_ACTIVITY_THRESHOLD;
    }
    // renamed from clause_new
    pub fn add_clause(&mut self, mut v: Vec<Lit>) -> bool {
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means totology.
        let mut result = false;
        for i in 0..v.len() {
            let li = v[i];
            let sat = self.assigned(li);
            if sat == LTRUE || li.negate() == l_ {
                v.clear();
                result = true;
                break;
            } else if sat != LFALSE && li != l_ {
                v[j] = li;
                j += 1;
                l_ = li;
            }
        }
        if result != true {
            v.truncate(j)
        }
        match v.len() {
            0 => result,
            1 => self.enqueue(v[0], NULL_CLAUSE),
            _ => {
                self.inject(Clause::new(false, v));
                true
            }
        }
    }
    pub fn lbd_of(&mut self, v: &[Lit]) -> usize {
        let k = 1 + self.lbd_key;
        self.lbd_key = k;
        if 1000_000 < k {
            self.lbd_key = 0;
        }
        let n = v.len();
        let mut cnt = 0;
        for i in 0..n {
            let l = self.vars[v[i].vi()].level;
            if self.lbd_seen[l] != k && l != 0 {
                self.lbd_seen[l] = k;
                cnt += 1;
            }
        }
        max(1, cnt)
    }
}

/// reduce_database
impl Solver {
    pub fn reduce_database(&mut self, simplify: bool) -> () {
        debug_assert!(
            !simplify || self.decision_level() == 0,
            "wrong invocation of reduce_database"
        );
        // if simplify {
        //     let mut assigned = 0;
        //     for v in &self.vars[1..] {
        //         if 0 < v.reason {
        //             assigned += 1;
        //         }
        //     }
        //     println!("  before simplify: {} {:?}", assigned, self.trail.iter().map(|l| &self.vars[l.vi()]).collect::<Vec<&Var>>());
        // }
        let end = self.clauses.len();
        let new_end = self.sort_clauses(simplify);
        self.rebuild_reason();
        if new_end < end {
            self.clauses.truncate(new_end);
        }
        if simplify || new_end == end {
            let mut fixed = 0;
            for c in &self.clauses {
                if c.rank <= 1 {
                    fixed += 1;
                }
            }
            self.fixed_len = fixed;
        }
        self.rebuild_watches();
        debug_assert_eq!(self.clauses[0].index, 0);
        let tag = if simplify { "simplify" } else { "drop 1/2" };
        println!(
            "# DB::{} {:>9} ({:>9}) => {:>9} / {:>9.1}",
            tag, end, self.fixed_len, new_end, self.max_learnts
        );
    }
    /// Note: this function changes self.clause_permutation.
    fn sort_clauses(&mut self, simplify: bool) -> usize {
        let start = if simplify { 1 } else { self.fixed_len };
        let nc = self.clauses.len();
        let mut requires = 0;
        let mut purges = 0;
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
        // reset the 'tmp' field
        for c in &mut self.clauses[start..] {
            (*c).tmp = 100;
        }
        // mark clauses that used as reasons
        for v in &self.vars[1..] {
            if 0 < v.reason {
                self.clauses[v.reason].tmp = 0;
            }
        }
        // set key
        let ac = 0.1 * self.cla_inc / (nc as f64);
        for ci in start..self.clauses.len() {
            unsafe {
                let mut c = &mut self.clauses[ci] as *mut Clause;
                if (*c).tmp == 0 {
                    requires += 1;
                } else if simplify && self.satisfies(&*c) {
                    (*c).rank = MAX;
                    (*c).tmp = MAX;
                    purges += 1;
                } else if (*c).rank == 0 {
                    (*c).tmp = 0;
                    requires += 1;
                } else {
                    requires += (*c).set_sort_key(ac);
                }
            }
        }
        // sort the range
        self.clauses[start..].sort_by_key(|c| c.tmp);
        // update permutation table.
        for i in 1..nc {
            let old = self.clauses[i].index;
            debug_assert!(0 < old, "0 index");
            self.clause_permutation[old] = i;
            self.clauses[i].index = i;
        }
        debug_assert!(self.clauses[0].index == 0, "NULL moved.");
        if simplify {
            min(start + max(requires, (nc - start) / 2), nc - purges)
        //start + requires + (nc - start - purges)
        } else {
            start + max(requires, (nc - start) / 2)
        }
    }
    fn rebuild_reason(&mut self) -> () {
        let len = self.clauses.len();
        let new_clause = &self.clause_permutation;
        for v in &mut self.vars[1..] {
            let ci = v.reason;
            if 0 < ci {
                v.reason = new_clause[ci];
                if v.reason == 0 || len < v.reason {
                    panic!("strange index for permutation {} {}", ci, len);
                }
            }
        }
    }
    fn rebuild_watches(&mut self) -> () {
        for w in &mut self.watches {
            w.clear();
        }
        debug_assert_eq!(self.clauses[0].index, 0);
        for c in &self.clauses[1..] {
            if 2 <= c.lits.len() {
                push_watch(&mut self.watches, c.index, c.lits[0], c.lits[1]);
            }
        }
        // self.dump(&format!("rebuild {}", self.learnts.len()));
    }
}

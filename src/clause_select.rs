use clause::*;
use solver::*;
use std::cmp::max;
use std::cmp::min;
use std::usize::MAX;
use types::*;
use watch::push_watch;

pub trait ClauseElimanation {
    fn bump_ci(&mut self, ci: ClauseIndex) -> ();
    fn decay_cla_activity(&mut self) -> ();
    fn reduce_database(&mut self) -> ();
    fn simplify_database(&mut self) -> ();
}

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

impl ClauseElimanation for Solver {
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
        self.cla_inc = self.cla_inc / CLAUSE_ACTIVITY_THRESHOLD;
    }
    fn reduce_database(&mut self) -> () {
        let end = self.clauses.len();
        let new_end = self.sort_clauses_for_reduction();
        self.rebuild_reason();
        if new_end < end {
            self.clauses.truncate(new_end);
        }
        self.rebuild_watches();
        debug_assert_eq!(self.clauses[0].index, 0);
        println!(
            "# DB::drop 1/2 {:>9} ({:>9}) => {:>9} / {:>9.1}",
            end, self.fixed_len, new_end, self.max_learnts
        );
    }
    fn simplify_database(&mut self) -> () {
        debug_assert_eq!(self.decision_level(), 0);
        let end = self.clauses.len();
        let new_end = self.sort_clauses_for_simplification();
        self.rebuild_reason();
        if new_end < end {
            self.clauses.truncate(new_end);
        }
        self.rebuild_watches();
        debug_assert_eq!(self.clauses[0].index, 0);
        println!(
            "# DB::simplify {:>9} ({:>9}) => {:>9} / {:>9.1}",
            end, self.fixed_len, new_end, self.max_learnts
        );
    }
}

/// returns 1 if this is good enough.
impl Clause {
    pub fn set_sort_key(&mut self, at: f64) -> usize {
        if self.rank == RANK_CONST {
            // only NULL and given
            self.tmp = 0;
            1
        } else if self.rank == 2 {
            self.tmp = RANK_NEED;
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
    fn rescale_clause_activity(&mut self) -> () {
        for i in self.fixed_len..self.clauses.len() {
            self.clauses[i].activity = self.clauses[i].activity / CLAUSE_ACTIVITY_THRESHOLD;
        }
        self.cla_inc /= CLAUSE_ACTIVITY_THRESHOLD;
    }
}

/// reduce_database
impl Solver {
    /// Note: this function changes self.clause_permutation.
    fn sort_clauses_for_reduction(&mut self) -> usize {
        let start = self.fixed_len;
        let nc = self.clauses.len();
        let mut requires = 0;
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
            (*c).tmp = RANK_MAX;
        }
        // mark clauses that used as reasons
        for v in &self.vars[1..] {
            if 0 < v.reason {
                self.clauses[v.reason].tmp = RANK_NEED;
            }
        }
        // set key
        let ac = 0.1 * self.cla_inc / (nc as f64);
        for ci in start..self.clauses.len() {
            let ref mut c = &mut self.clauses[ci];
            debug_assert_ne!(c.rank, RANK_CONST);
            if c.tmp == RANK_NEED {
                requires += 1;
            } else {
                requires += c.set_sort_key(ac);
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
        println!(
            "# DB::drop 1/2 {:>9} ({:>9}) => {:>9} / {:>9.1}",
            nc,
            self.fixed_len,
            start + max(requires, (nc - start) / 2),
            self.max_learnts
        );
        self.fixed_len += requires;
        start + max(requires, (nc - start) / 2)
    }
    fn sort_clauses_for_simplification(&mut self) -> usize {
        let nc = self.clauses.len();
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
        // set key
        for ci in 1..self.clauses.len() {
            unsafe {
                let c = &mut self.clauses[ci] as *mut Clause;
                if self.satisfies(&self.clauses[ci]) {
                    (*c).tmp = MAX;
                    purges += 1;
                } else {
                    (*c).tmp = (*c).rank;
                }
            }
        }
        self.clauses.retain(|ref c| c.tmp < MAX);
        let nn = self.clauses.len();
        debug_assert_eq!(nn, nc - purges);
        for i in 1..nn {
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
            match c.tmp {
                RANK_CONST | RANK_NEED => {
                    c0 += 1;
                }
                _ => {
                    break;
                }
            }
        }
        self.fixed_len = c0;
        // DEBUG: check consistency
        // {
        //     let mut c1 = 0;
        //     for c in &self.clauses[..] {
        //         match c.tmp {
        //             RANK_CONST|RANK_NEED => { c1 += 1; }
        //             _ => { }
        //         }
        //     }
        //     debug_assert_eq!(c0, c1);
        //     debug_assert!(self.clauses[0].index == 0, "NULL moved.");
        // }
        // println!(
        //     "# DB::simplify {:>9} ({:>9}) => {:>9} / {:>9.1}",
        //     nc, self.fixed_len, nn, self.max_learnts
        // );
        nn
    }
    fn rebuild_reason(&mut self) -> () {
        let new_clause = &self.clause_permutation;
        for v in &mut self.vars[1..] {
            let ci = v.reason;
            if 0 < ci {
                v.reason = new_clause[ci];
                // if v.reason == 0 || len < v.reason {
                //     // println!("trail{:?}", self.trail.iter().map(|l| l.int()).collect::<Vec<i32>>());
                //     println!("lim {}", self.trail_lim.len());
                //     panic!(
                //         "strange index for permutation v{:?} {} < {}",
                //         v, len, v.reason
                //     );
                // }
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

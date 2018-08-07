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
    /// renamed from simplfy
    fn removable(&self, ci: ClauseIndex) -> bool {
        let c = self.iref_clause(ci);
        for l in &c.lits {
            if self.lit2asg(*l) == LTRUE {
                return true;
            }
        }
        false
    }
    // adapt delayed update of watches
    fn propagate(&mut self, _l: Lit) -> Option<ClauseIndex> {
        loop {
            let p = self.trail[1 + self.q_head];
            self.q_head += 1;
            self.stats[StatIndex::NumOfPropagation as usize] += 1;
            {
                let wl = self.watches[p as usize].len();
                let false_lit = p.negate();
                'next_clause: for mut wi in 0..wl {
                    let Watch {
                        other: blocker,
                        by: ci,
                        ..
                    } = self.watches[p as usize][wi];
                    // We need a storage to keep a literal which is the destination of propagation.
                    // * candidate 1, Watch.to, better about reference locality if other is satisfied.
                    // * candidate 2. Clause.tmp
                    let bv = if blocker == 0 {
                        LFALSE
                    } else {
                        self.lit2asg(blocker)
                    };
                    if bv == LTRUE {
                        self.watches[p as usize][wi].to = p;
                        continue 'next_clause;
                    }
                    let mut first = 0;
                    let mut clen = 0;
                    let mut c = 0 as *mut Clause;
                    let mut cid = NULL_CLAUSE;
                    unsafe {
                        c = self.mref_clause(ci) as *mut Clause;
                        cid = (*c).index;
                        let l0 = (*c).lits[0];
                        first = if false_lit == l0 {
                            let l1 = (*c).lits[1];
                            (*c).lits[0] = l1;
                            (*c).lits[1] = l0;
                            l1
                        } else {
                            l0
                        };
                        clen = (*c).lits.len();
                    }
                    if self.lit2asg(first) == LTRUE {
                        self.watches[p as usize][wi].to = p;
                        continue 'next_clause;
                    }
                    for k in 2..clen {
                        unsafe {
                            let lk = (*c).lits[k];
                            if self.lit2asg(lk) != LFALSE {
                                (*c).lits[1] = lk;
                                self.watches[p as usize][wi].to = lk.negate();
                                break 'next_clause;
                            }
                        }
                    }
                    // conflict!
                    return Some(cid);
                }
                // No conflict: so let's move them!
                // use watches[0] to keep watches that don't move anywhere, temporally.
                self.watches[0].clear();
                loop {
                    match self.watches[p as usize].pop() {
                        Some(w) => self.watches[w.to as usize].push(w),
                        None => break,
                    }
                }
                loop {
                    match self.watches[0].pop() {
                        Some(w) => self.watches[p as usize].push(w),
                        None => break,
                    }
                }
            }
            if self.trail.len() <= self.q_head {
                return None;
            }
        }
    }
    fn analyze(&mut self, confl: ClauseIndex) -> (u32, Clause) {
        self.an_learnt_lits.clear();
        self.an_learnt_lits.push(0);
        let dl = self.decision_level();
        let mut ci = confl;
        let mut c = 0 as *mut Clause;
        let mut p = BOTTOM;
        let mut ti = self.trail.len() - 1; // trail index
        let mut b = 0; // backtrack level
        let mut path_cnt = 0;
        loop {
            unsafe {
                c = self.mref_clause(ci);
                let d = (*c).rank;
                if 0 != d {
                    self.bump_ci(ci);
                }
                let sc = (*c).lits.len();
                let nblevel = self.lbd_of(&(*c).lits);
                if 2 < d && nblevel + 1 < d {
                    (*c).rank = nblevel;
                }
                for j in (if p == BOTTOM { 0 } else { 1 })..sc {
                    let q = (*c).lits[j];
                    let vi = q.vi();
                    let l = self.vars[vi].level;
                    if self.an_seen[vi] == 0 && 0 < l {
                        self.bump_vi(vi);
                        self.an_seen[vi] = 1;
                        if dl <= l {
                            let ri: ClauseIndex = self.vars[vi].reason;
                            if ri != NULL_CLAUSE && self.iref_clause(ri).rank != 0 {
                                self.an_last_dl.push(q);
                            }
                            path_cnt += 1;
                        } else {
                            self.an_learnt_lits.push(q);
                            b = max(b, l);
                        }
                    }
                }
                // set the index of the next literal to ti
                loop {
                    if self.an_seen[self.trail[ti].vi()] == 0 {
                        ti -= 1;
                    } else {
                        break;
                    }
                }
                let next_p: Lit = self.trail[ti];
                let next_vi: VarIndex = next_p.vi();
                ci = self.vars[next_vi].reason;
                self.an_seen[next_vi] = 0;
                if 1 < path_cnt {
                    ti -= 1;
                    path_cnt -= 1;
                } else {
                    self.an_learnt_lits[0] = next_p.negate();
                    break;
                }
            }
        }
        let level_to_return = b;
        // simlpify phase
        let n = self.an_learnt_lits.len();
        let l0 = self.an_learnt_lits[0];
        self.an_stack.clear();
        self.an_to_clear.clear();
        self.an_to_clear.push(l0);
        let mut levels = 0;
        for i in 1..n {
            let l = self.an_learnt_lits[i];
            self.an_to_clear.push(l);
            levels |= 63 & self.vars[l.vi()].level;
        }
        (
            level_to_return as u32,
            Clause::new(self.an_learnt_lits.clone()),
        )
    }
    pub fn reduce_database(&mut self) -> () {
        let keep = self.sort_learnts();
        self.rebuild_reason();
        self.rebuild_watches();
        // self.check_clause_index_consistency();
        self.learnts.truncate(keep);
    }
    /// Note: this function changes self.learnt_permutation.
    fn sort_learnts(&mut self) -> usize {
        let nc = self.learnts.len();
        let mut requires = 0;
        for c in &self.learnts {
            requires += c.set_sort_key();
        }
        self.learnts.sort_by_key(|c| c.tmp);
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
    fn search(&mut self) -> () {}
    pub fn solve(&mut self) -> () {
        self.propagate(0);
    }
    fn unsafe_enqueue(&mut self, l: Lit, ci: ClauseIndex) -> () {}
}

fn simplify(_s: &mut Solver) -> () {}

#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use clause::*;
use solver::*;
use std::cmp::max;
use std::result::Result;
use types::*;

impl Solver {
    /// renamed from newLearntClause
    pub fn new_learnt(&mut self, v: Vec<Lit>) -> usize {
        let k = v.len();
        if k == 1 {
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
    fn propagate(&mut self) -> Option<ClauseIndex> {
        // println!("> propagate at {}", self.decision_level());
        loop {
            if self.trail.len() <= self.q_head {
                // println!("<  propagate done");
                return None;
            }
            // println!(
            //     "  self.trail.len {}, self.q_head {}",
            //     self.trail.len(),
            //     self.q_head
            // );
            let p = self.trail[self.q_head];
            self.q_head += 1;
            self.stats[StatIndex::NumOfPropagation as usize] += 1;
            {
                let wl = self.watches[p as usize].len();
                let false_lit = p.negate();
                'next_clause: for mut wi in 0..wl {
                    // println!(" next_clause: {}", wi);
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
                    unsafe {
                        let c = self.mref_clause(ci) as *mut Clause;
                        let l0 = (*c).lits[0];
                        let first = if false_lit == l0 {
                            let l1 = (*c).lits[1];
                            (*c).lits[0] = l1;
                            (*c).lits[1] = l0;
                            l1
                        } else {
                            l0
                        };
                        let fv = self.lit2asg(first);
                        if fv == LTRUE {
                            // update watch by the cached literal
                            self.watches[p as usize][wi].to = p;
                            continue 'next_clause;
                        }
                        for k in 2..(*c).lits.len() {
                            let lk = (*c).lits[k];
                            if self.lit2asg(lk) != LFALSE {
                                (*c).lits[1] = lk;
                                (*c).lits[k] = false_lit;
                                // update watch
                                self.watches[p as usize][wi].to = lk.negate();
                                continue 'next_clause;
                            }
                        }
                        if fv == LFALSE {
                            // conflict
                            // println!("  found a conflict by {}", (*c));
                            // println!(
                            //     "  under the assigment {:?}",
                            //     self.trail.iter().map(|l| l.int()).collect::<Vec<i32>>()
                            // );
                            // println!("  during propagating {}", p.int());
                            // println!("< propagate");
                            return Some((*c).index); // TODO why don't you return `*c` itself?
                        } else {
                            // unit propagation
                            // println!("  unit propagation {} by {}", first.int(), (*c));
                            // println!(
                            //     "  under the assigment {:?}",
                            //     self.trail.iter().map(|l| l.int()).collect::<Vec<i32>>()
                            // );
                            self.watches[p as usize][wi].to = p;
                            self.unsafe_enqueue(first, ci);
                        }
                    }
                }
                // No conflict: so let's move them!
                // use watches[0] to keep watches that don't move anywhere, temporally.
                // println!("  update watches");
                self.watches[0].clear();
                loop {
                    // println!("   remain: {}", self.watches[p as usize].len());
                    match self.watches[p as usize].pop() {
                        Some(w) => {
                            assert_ne!(w.to, 0);
                            if w.to == p {
                                self.watches[0].push(w)
                            } else {
                                // println!("  move a watch for {} to {}", w.by, w.to.int());
                                self.watches[w.to as usize].push(w)
                            }
                        }
                        None => break,
                    }
                }
                loop {
                    match self.watches[0].pop() {
                        Some(w) => {
                            // println!("  loop back by {} to {}", w.by, w.to.int());
                            assert_eq!(w.to, p);
                            self.watches[p as usize].push(w);
                        }
                        None => break,
                    }
                }
                // println!("  propagate done");
            }
        }
    }
    fn analyze(&mut self, confl: ClauseIndex) -> (u32, Vec<Lit>) {
        self.an_learnt_lits.clear();
        self.an_learnt_lits.push(0);
        let dl = self.decision_level();
        let mut ci = confl;
        let mut p = NULL_LIT;
        let mut ti = self.trail.len() - 1; // trail index
        let mut b = 0; // backtrack level
        let mut path_cnt = 0;
        loop {
            unsafe {
                let c = self.mref_clause(ci) as *mut Clause;
                // println!("  analyze.loop {}", (*c));
                let d = (*c).rank;
                if 0 != d {
                    self.bump_ci(ci);
                }
                let sc = (*c).lits.len();
                let nblevel = self.lbd_of(&(*c).lits);
                if 2 < d && nblevel + 1 < d {
                    (*c).rank = nblevel;
                }
                for j in (if p == NULL_LIT { 0 } else { 1 })..sc {
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
                // println!("  analyze.loop 2");
                // set the index of the next literal to ti
                loop {
                    if self.an_seen[self.trail[ti].vi()] == 0 {
                        if ti == 0 {
                            panic!("aaaa");
                        };
                        ti -= 1;
                    } else {
                        ti -= 1;
                        break;
                    }
                }
                // println!("  analzye.loop 3");
                p = self.trail[ti];
                let next_vi: VarIndex = p.vi();
                ci = self.vars[next_vi].reason;
                self.an_seen[next_vi] = 0;
                if 1 < path_cnt {
                    // ti -= 1;
                    path_cnt -= 1;
                } else {
                    self.an_learnt_lits[0] = p.negate();
                    break;
                }
            }
        }
        // println!("  analyze.loop terminated");
        let level_to_return = b;
        // simlpify phase
        let n = self.an_learnt_lits.len();
        let l0 = self.an_learnt_lits[0];
        self.an_stack.clear();
        self.an_to_clear.clear();
        self.an_to_clear.push(l0);
        let mut levels: u64 = 0;
        for i in 1..n {
            let l = self.an_learnt_lits[i];
            self.an_to_clear.push(l);
            levels |= 63 & (self.vars[l.vi()].level as u64);
        }
        // println!("  analyze.loop 4 n = {}", n);
        let mut i = 1;
        let mut j = 1;
        loop {
            println!("  analyze.loop for simplify {} {}", i, n);
            if i == n {
                self.an_learnt_lits.truncate(j + 1);
                break;
            }
            let l = self.an_learnt_lits[i];
            if self.vars[l.vi()].reason == NULL_CLAUSE {
                self.an_learnt_lits[j] = l;
                j += 1;
            } else if !self.analyze_removable(l, levels) {
                self.an_learnt_lits[j] = l;
                j += 1;
            }
            i += 1;
        }
        // glucose heuristics
        // println!("  analyze.loop 5");
        let r = self.an_learnt_lits.len();
        for i in 0..self.an_last_dl.len() {
            let l = self.an_last_dl[i];
            let vi = l.vi();
            let ci = self.vars[vi].reason;
            let len = self.iref_clause(ci).lits.len();
            if r < len {
                self.bump_vi(vi);
            }
        }
        self.an_last_dl.clear();
        for l in &self.an_to_clear {
            self.an_seen[l.vi()] = 0;
        }
        println!(
            "new learnt: {:?}",
            self.an_learnt_lits
                .iter()
                .map(|l| l.int())
                .collect::<Vec<i32>>()
        );
        // println!("  analyze terminated");
        (level_to_return as u32, self.an_learnt_lits.clone())
    }
    fn analyze_removable(&mut self, l: Lit, min_level: u64) -> bool {
        self.an_stack.clear();
        self.an_stack.push(l);
        let top1 = self.an_to_clear.len();
        loop {
            // println!("analyze_removable.loop {:?}", self.an_stack);
            if self.an_stack.is_empty() {
                return true;
            }
            let sl = self.an_stack.pop().unwrap();
            let ci = self.vars[sl.vi()].reason;
            let c = self.iref_clause(ci) as *const Clause;
            unsafe {
                for q in &(*c).lits {
                    let vi = q.vi();
                    let lv = self.vars[vi].level as u64;
                    if self.an_seen[vi] != 1 && lv != 0 {
                        if self.vars[vi].reason != NULL_CLAUSE && 0 != (1 << lv & 63) & min_level {
                            self.an_seen[vi] = 1;
                            self.an_stack.push(*q);
                            self.an_to_clear.push(*q);
                        } else {
                            let top2 = self.an_to_clear.len();
                            for _ in top1..top2 {
                                self.an_seen[self.an_to_clear.pop().unwrap().vi()] = 0;
                            }
                            return false;
                        }
                    }
                }
            }
        }
    }
    fn analyze_final(&mut self, ci: ClauseIndex, skip_first: bool) -> () {
        self.conflicts.clear();
        if self.root_level != 0 {
            unsafe {
                let c = self.iref_clause(ci) as *const Clause;
                for l in &(*c).lits[(if skip_first { 1 } else { 0 })..] {
                    let vi = l.vi();
                    if 0 < self.vars[vi].level {
                        self.an_seen[vi] = 1;
                    }
                }
            }
            let tl0 = self.trail_lim[0];
            let start = if self.trail_lim.len() <= self.root_level {
                self.trail.len()
            } else {
                self.trail_lim[self.root_level]
            };
            for i in (tl0..start).rev() {
                let l: Lit = self.trail[i];
                let vi = l.vi();
                if self.an_seen[vi] == 1 {
                    if self.vars[vi].reason == NULL_CLAUSE {
                        self.conflicts.push(l.negate());
                    } else {
                        let c = self.iref_clause(ci) as *const Clause;
                        unsafe {
                            for i in 1..(*c).lits.len() {
                                let vi = (*c).lits[i].vi();
                                if 0 < self.vars[vi].level {
                                    self.an_seen[vi] = 1;
                                }
                            }
                        }
                    }
                }
                self.an_seen[vi] = 0;
            }
        }
    }
    pub fn reduce_database(&mut self) -> () {
        let keep_c = self.sort_clauses();
        let keep_l = self.sort_learnts();
        self.rebuild_reason();
        self.rebuild_watches();
        // self.check_clause_index_consistency();
        self.clauses.truncate(keep_c);
        self.learnts.truncate(keep_l);
    }
    /// Note: this function changes self.clause_permutation.
    fn sort_clauses(&mut self) -> usize {
        if self.decision_level() == 0
            && self.stats[StatIndex::NumOfGroundVar as usize] < self.num_assigns() as i64
        {
            // TODO
            // 1. run tautology checker
            // 2. purge some out of clauses
            // 3. renumber remains
            self.num_clauses()
        } else {
            self.num_clauses()
        }
    }
    /// Note: this function changes self.learnt_permutation.
    fn sort_learnts(&mut self) -> usize {
        let mut requires = 0;
        let nc = self.learnts.len();
        {
            // set key
            let ac = 0.1 * self.cla_inc / (nc as f64);
            for c in &mut self.learnts {
                requires += c.set_sort_key(ac);
            }
        }
        {
            // check locked
            let nv = self.vars.len();
            for vi in 1..nv + 1 {
                let ci = self.vars[vi].reason;
                if 0 < ci {
                    let val = self.learnts[ci as usize].tmp;
                    if 0 < val {
                        self.learnts[ci as usize].tmp = 0;
                        requires += 1;
                    }
                }
            }
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
        for v in &mut self.vars[1..] {
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
        for w in &mut self.watches {
            w.clear();
        }
        for c in &self.clauses {
            register_to_watches(&mut self.watches, c.index, c.lits[0], c.lits[1]);
        }
        for c in &self.learnts {
            register_to_watches(&mut self.watches, c.index, c.lits[0], c.lits[1]);
        }
    }
    fn search(&mut self) -> bool {
        // println!("search");
        let delta = (self.num_vars as f64).sqrt();
        let root_lv = self.root_level;
        let mut to_restart = false;
        loop {
            let ret = self.propagate();
            let d = self.decision_level();
            println!("search called propagate and it returned {:?} at {}", ret, d);
            match ret {
                Some(ci) => {
                    self.stats[StatIndex::NumOfBackjump as usize] += 1;
                    if d == self.root_level {
                        println!("  it's UNSAT");
                        self.analyze_final(ci, false);
                        return false;
                    } else {
                        let (backtrack_level, v) = self.analyze(ci);
                        println!(
                            " conflict analyzed {:?}",
                            v.iter().map(|l| l.int()).collect::<Vec<i32>>()
                        );
                        self.cancel_until(max(backtrack_level as usize, root_lv));
                        println!(" backtracked to {}", backtrack_level);
                        let lbd = self.new_learnt(v);
                        let k = self.an_learnt_lits.len();
                        if k == 1 {
                            self.vars[self.an_learnt_lits[0].vi()].level = 0;
                        }
                        self.decay_var_activity();
                        self.decay_cla_activity();
                        self.learnt_size_cnt -= 1;
                        if self.learnt_size_cnt == 0 {
                            let t_ = 1.5 * self.learnt_size_adj;
                            self.learnt_size_adj = t_;
                            self.learnt_size_cnt = t_ as u64;
                            self.max_learnts += delta;
                            to_restart = self.should_restart(lbd, d);
                            continue;
                        }
                    }
                    // println!(" search loop conflict terminated");
                }
                None => {
                    // println!(" search loop enter a new level");
                    // if d == 0 { simplify_db() };
                    let na = self.num_assigns();
                    if self.max_learnts as usize + na < self.learnts.len() {
                        self.reduce_database();
                    }
                    if na == self.num_vars {
                        return true;
                    } else if to_restart {
                        self.cancel_until(root_lv);
                        to_restart = false;
                    } else {
                        // println!(
                        //     " trail     {:?}",
                        //     self.trail.iter().map(|l| l.int()).collect::<Vec<i32>>()
                        // );
                        // println!(" trail lim {:?}", self.trail_lim);
                        // println!(" {:?}", self.var_order);
                        // println!("  num_assigns = {}", na);
                        let vi = self.select_var();
                        // println!(" search loop find a new decision var");
                        assert_ne!(vi, 0);
                        // println!(" {:?}", self.var_order);
                        if vi != 0 {
                            let p = self.vars[vi].phase;
                            self.unsafe_assume(vi.lit(p));
                        }
                    }
                }
            }
            // println!(" search loop terminate");
        }
    }
    pub fn solve(&mut self) -> Result<Certificate, SolverException> {
        // TODO deal with assumptons
        // s.root_level = 0;
        let status = self.search();
        if status && self.ok == LTRUE {
            let mut result = Vec::new();
            for vi in 1..self.num_vars + 1 {
                if self.vars[vi].assign == LTRUE {
                    result.push(vi as i32);
                } else if self.vars[vi].assign == LFALSE {
                    result.push(0 - vi as i32);
                }
            }
            self.cancel_until(0);
            Ok(Certificate::SAT(result))
        } else if !status && self.ok == LFALSE {
            self.cancel_until(0);
            let mut v = Vec::new();
            for l in &self.conflicts {
                v.push(l.int());
            }
            Ok(Certificate::UNSAT(v))
        } else {
            self.cancel_until(0);
            Err(SolverException::InternalInconsistent)
        }
    }
    fn unsafe_enqueue(&mut self, l: Lit, ci: ClauseIndex) -> () {
        let vi = l.vi();
        let dl = self.decision_level();
        let v = &mut self.vars[vi];
        v.assign = l.lbool();
        v.level = dl;
        v.reason = ci;
        self.trail.push(l)
    }
    fn unsafe_assume(&mut self, l: Lit) -> () {
        let len = self.trail.len();
        self.trail_lim.push(len);
        self.unsafe_enqueue(l, NULL_CLAUSE);
    }
}

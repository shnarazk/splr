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
        // level max
        let mut lvm = 0;
        // seek a literal with max level
        for i in 0..c.lits.len() {
            let vi = c.lits[i].vi();
            let lv = self.vars[vi].level;
            if self.vars[vi].assign != BOTTOM && lvm < lv {
                j = i;
                lvm = lv;
            }
        }
        c.lits.swap(1, j);
        let l0 = c.lits[0];
        let lbd = self.lbd_of(&c.lits);
        c.rank = lbd;
        let ci = self.inject(true, c);
        self.bump_ci(ci);
        self.unsafe_enqueue(l0, ci);
        lbd
    }
    /// renamed from simplfy
    fn removable(&self, ci: ClauseIndex) -> bool {
        let c = self.iref_clause(ci);
        for l in &c.lits {
            if self.assigned(*l) == LTRUE {
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
                        // self.lit2asg(blocker) FIXME for debug
                        LFALSE
                    };
                    if bv == LTRUE {
                        self.watches[p as usize][wi].to = p;
                        continue 'next_clause;
                    }
                    unsafe {
                        let c = self.mref_clause(ci) as *mut Clause;
                        assert_eq!(ci, (*c).index);
                        if !(false_lit == (*c).lits[0] || false_lit == (*c).lits[1]) {
                            panic!(
                                "Watch literals error by {} ({}, {}) for propagate({})",
                                (*c),
                                (*c).lits[0].int(),
                                (*c).lits[1].int(),
                                p.int()
                            );
                        }
                        // Make sure tha false literal is lits[1]; the last literal in unit clause is lits[0].
                        if (*c).lits[0] == false_lit {
                            (*c).lits.swap(0, 1);
                        }
                        let first = (*c).lits[0];
                        assert_eq!(false_lit, (*c).lits[1]);
                        let fv = self.assigned(first);
                        if fv == LTRUE {
                            // update watch by the cached literal; this is a satisfied, unit clause.
                            self.watches[p as usize][wi].to = p;
                            continue 'next_clause;
                        }
                        self.watches[p as usize][wi].other = first;
                        for k in 2..(*c).lits.len() {
                            let lk = (*c).lits[k];
                            if self.assigned(lk) != LFALSE {
                                (*c).tmp = k as i64;
                                // update watch
                                self.watches[p as usize][wi].to = lk.negate();
                                continue 'next_clause;
                            }
                        }
                        if fv == LFALSE {
                            // conflict
                            // println!("  found a conflict variable {} by {}", first.vi(), (*c));
                            return Some((*c).index); // TODO why don't you return `*c` itself?
                        } else {
                            // unit propagation
                            // println!("  unit propagation {} by {}", first.int(), (*c));
                            (*c).tmp = 1;
                            self.watches[p as usize][wi].to = p;
                            assert_eq!(first, (*c).lits[0]);
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
                                unsafe {
                                    let c = self.mref_clause(w.by) as *mut Clause;
                                    let k = (*c).tmp as usize;
                                    // println!("moving {} with {} to {}", (*c), k, w.to.int());
                                    (*c).lits.swap(1, k);
                                }
                                // println!("move {} to {}", w.by, w.to.int());
                                self.watches[w.to as usize].push(w);
                            }
                        }
                        None => break,
                    }
                }
                assert_eq!(self.watches[p as usize].is_empty(), true);
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
        for mut l in &mut self.an_seen {
            *l = 0;
        }
        // self.dump("analyze");
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
                assert_ne!(ci, NULL_CLAUSE);
                let c = self.mref_clause(ci) as *mut Clause;
                // println!("  analyze.loop {}", (*c));
                let d = (*c).rank;
                if 0 != d {
                    self.bump_ci(ci);
                }
                let nblevel = self.lbd_of(&(*c).lits);
                if 2 < d && nblevel + 1 < d {
                    (*c).rank = nblevel;
                }
                // println!("{}を対応", (*c));
                for j in (if p == NULL_LIT { 0 } else { 1 })..(*c).lits.len() {
                    let q = (*c).lits[j];
                    let vi = q.vi();
                    let l = self.vars[vi].level;
                    assert_ne!(self.vars[vi].assign, BOTTOM);
                    if self.an_seen[vi] == 0 && 0 < l {
                        self.bump_vi(vi);
                        self.an_seen[vi] = 1;
                        if dl <= l {
                            // println!(
                            //     "{} はレベル{}なのでフラグを立てる",
                            //     q.int(),
                            //     l
                            // );
                            path_cnt += 1;
                            if 0 < self.vars[vi].reason {
                                self.an_last_dl.push(q);
                            }
                        } else {
                            // println!("{} はレベル{}なので採用", q.int(), l);
                            self.an_learnt_lits.push(q);
                            b = max(b, l);
                        }
                    } else {
                        // println!("{} はもうフラグが立っているかグラウンドしている{}ので無視", q.int(), l);
                    }
                }
                // set the index of the next literal to ti
                while self.an_seen[self.trail[ti].vi()] == 0 {
                    // println!(
                    //     "{} はフラグが立ってないので飛ばす",
                    //     self.trail[ti].int()
                    // );
                    ti -= 1;
                }
                p = self.trail[ti];
                {
                    let next_vi: VarIndex = p.vi();
                    ci = self.vars[next_vi].reason;
                    // println!("{} にフラグが立っている。この時path数は{}, そのreason {}を探索", next_vi, path_cnt - 1, ci);
                    self.an_seen[next_vi] = 0;
                }
                path_cnt -= 1;
                if path_cnt <= 0 {
                    break;
                }
                ti -= 1;
            }
        }
        self.an_learnt_lits[0] = p.negate();
        // println!(
        //     "最後に{}を採用して{:?}",
        //     p.negate().int(),
        //     self.an_learnt_lits
        //         .iter()
        //         .map(|l| l.int())
        //         .collect::<Vec<i32>>()
        // );
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
            levels |= 63 & ((self.vars[l.vi()].level % 60) as u64);
        }
        // println!("  analyze.loop 4 n = {}", n);
        let mut i = 1;
        let mut j = 1;
        loop {
            // println!("  analyze.loop for simplify {} {}", i, n);
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
        self.an_learnt_lits.truncate(j);
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
        // println!(
        //     "new learnt: {:?}",
        //     self.an_learnt_lits
        //         .iter()
        //         .map(|l| l.int())
        //         .collect::<Vec<i32>>()
        // );
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
                    let lv = self.vars[vi].level % 60;
                    if self.an_seen[vi] != 1 && lv != 0 {
                        if self.vars[vi].reason != NULL_CLAUSE
                            && 0u64 != (1u64 << lv) & min_level as u64
                        {
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
        // panic!("not implemented");
        let keep_c = self.sort_clauses();
        let keep_l = self.sort_learnts();
        self.rebuild_reason();
        // self.check_clause_index_consistency();
        println!("keep_c {} -> {} {}", keep_c, keep_l, self.max_learnts);
        self.clauses.truncate(keep_c);
        self.learnts.truncate(keep_l);
        self.rebuild_watches();
        println!("< rebuild_database done");
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
            self.clauses.len()
        } else {
            self.clauses.len()
        }
    }
    /// Note: this function changes self.learnt_permutation.
    fn sort_learnts(&mut self) -> usize {
        let mut requires = 0;
        let nc = self.learnts.len();
        if self.learnt_permutation.len() < nc {
            unsafe {
                self.learnt_permutation.reserve(nc + 1);
                self.learnt_permutation.set_len(nc + 1);
            }
        }
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
            for vi in 1..nv {
                let ci = self.vars[vi].reason;
                if 0 < ci {
                    let val = self.learnts[ci as usize].tmp;
                    if 0 < val {
                        self.learnts[ci as usize].tmp = -1;
                        requires += 1;
                    }
                }
            }
        }
        let n = max(requires, nc / 2);
        self.learnts.sort_by_key(|c| c.tmp);
        // println!("sorted {:?}", self.learnts);
        for i in 1..nc {
            let old = self.learnts[i].index as usize;
            self.learnt_permutation[old] = i as i64;
            self.learnts[i].index = i as ClauseIndex;
            self.learnts[i].tmp = 0;
        }
        self.learnt_permutation[0] = 0;
        // println!("done");
        max(requires, nc / 2)
    }
    fn rebuild_reason(&mut self) -> () {
        let perm = &self.learnt_permutation;
        // println!("perm {:?}", perm);
        for v in &mut self.vars[1..] {
            let ci = v.reason;
            if 0 < ci {
                v.reason = perm[ci as usize];
            }
        }
    }
    fn rebuild_watches(&mut self) -> () {
        // Firstly, clear everything.
        // for i in 1..self.watches.len() {
        //     let w = &mut self.watches[i];
        //     w.clear();
        // }
        for w in &mut self.watches {
            w.clear();
        }
        // assert_eq!(self.clauses[0].index, 0);
        for c in &self.clauses[1..] {
            if 2 <= c.lits.len() {
                register_to_watches(&mut self.watches, c.index, c.lits[0], c.lits[1]);
            }
        }
        // assert_eq!(self.learnts[0].index, 0);
        for c in &self.learnts[1..] {
            if 2 <= c.lits.len() {
                // println!("register {}", c.index);
                register_to_watches(&mut self.watches, c.index, c.lits[0], c.lits[1]);
            }
        }
        // self.dump(&format!("rebuild {}", self.learnts.len()));
    }
    fn search(&mut self) -> bool {
        // println!("search");
        let delta = 800.0; // (self.num_vars as f64).sqrt();
        let root_lv = self.root_level;
        let mut to_restart = false;
        loop {
            // self.dump("search");
            let ret = self.propagate();
            let d = self.decision_level();
            // println!("search called propagate and it returned {:?} at {}", ret, d);
            match ret {
                Some(ci) => {
                    self.stats[StatIndex::NumOfBackjump as usize] += 1;
                    if d == self.root_level {
                        println!("  it's UNSAT");
                        self.analyze_final(ci, false);
                        return false;
                    } else {
                        // self.dump(" before analyze");
                        let (backtrack_level, v) = self.analyze(ci);
                        // self.dump("analyzed");
                        // println!(
                        //     " conflict analyzed {:?}",
                        //     v.iter().map(|l| l.int()).collect::<Vec<i32>>()
                        // );
                        self.cancel_until(max(backtrack_level as usize, root_lv));
                        // println!(" backtracked to {}", backtrack_level);
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
                        println!("  SOLVED");
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
                        if vi == 0 {
                            self.dump("no more decision canditate");
                        }
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
        // if ci == NULL_CLAUSE {
        //     println!("unsafe_enqueue decide: {}", l.int());
        // } else {
        //     println!("unsafe_enqueue imply: {} by {}", l.int(), ci);
        // }
        let dl = self.decision_level();
        let v = &mut self.vars[l.vi()];
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

use clause::*;
use clause_manage::ClauseManagement;
use solver::Solver;
use std::cmp::max;
use types::*;
use var_select::VarSelect;

pub trait CDCL {
    fn analyze(&mut self, confl: ClauseIndex) -> usize;
    fn analyze_final(&mut self, ci: ClauseIndex, skip_first: bool) -> ();
}

impl CDCL for Solver {
    fn analyze(&mut self, confl: ClauseIndex) -> usize {
        for mut l in &mut self.an_seen {
            debug_assert_eq!(*l, 0);
            // *l = 0;
        }
        // self.dump("analyze");
        self.an_learnt_lits.clear();
        self.an_learnt_lits.push(0);
        let dl = self.decision_level();
        let mut ci = confl;
        let mut p = NULL_LIT;
        let mut ti = self.trail.len() - 1; // trail index
        let mut b: usize = 0; // backtrack level
        let mut path_cnt = 0;
        loop {
            unsafe {
                let c = &mut self.clauses[ci] as *mut Clause;
                debug_assert_ne!(ci, NULL_CLAUSE);
                // println!("  analyze.loop {}", (*c));
                let d = (*c).rank;
                if RANK_NEED < d {
                    self.bump_ci(ci);
                    let nblevel = self.lbd_of(&(*c).lits);
                    if nblevel < d {
                        (*c).rank = nblevel;
                    }
                }
                // println!("{}を対応", (*c));
                for q in &(*c).lits[if p == NULL_LIT { 0 } else { 1 }..] {
                    let vi = q.vi();
                    let l = self.vars[vi].level;
                    debug_assert_ne!(self.vars[vi].assign, BOTTOM);
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
                                self.an_last_dl.push(*q);
                            }
                        } else {
                            // println!("{} はレベル{}なので採用", q.int(), l);
                            self.an_learnt_lits.push(*q);
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
        //     p.negate().int(), vec2int(self.an_learnt_lits)
        // );
        // simplify phase
        let n = self.an_learnt_lits.len();
        let l0 = self.an_learnt_lits[0];
        self.an_stack.clear();
        self.an_to_clear.clear();
        self.an_to_clear.push(l0);
        self.an_level_map.clear();
        for i in 1..n {
            let l = self.an_learnt_lits[i];
            self.an_to_clear.push(l);
            self.an_level_map.insert(self.vars[l.vi()].level);
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
            } else if !self.analyze_removable(l) {
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
            let len = self.clauses[ci].lits.len();
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
        //     vec2int(self.an_learnt_lits)
        // );
        // println!("  analyze terminated");
        // find correct backtrack level from remaining literals
        let mut level_to_return = 0;
        if self.an_learnt_lits.len() != 1 {
            let mut max_i = 1;
            level_to_return = self.vars[self.an_learnt_lits[max_i].vi()].level;
            for i in 2..self.an_learnt_lits.len() {
                let l = &self.an_learnt_lits[i];
                let lv = self.vars[l.vi()].level;
                if level_to_return < lv {
                    level_to_return = lv;
                    max_i = i;
                }
            }
            self.an_learnt_lits.swap(1, max_i);
        }
        for l in &self.an_to_clear {
            self.an_seen[l.vi()] = 0;
        }
        level_to_return
    }
    fn analyze_final(&mut self, ci: ClauseIndex, skip_first: bool) -> () {
        self.conflicts.clear();
        if self.root_level != 0 {
            for l in &self.clauses[ci].lits[(if skip_first { 1 } else { 0 })..] {
                let vi = l.vi();
                if 0 < self.vars[vi].level {
                    self.an_seen[vi] = 1;
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
                        for l in &self.clauses[ci].lits[1..] {
                            let vi = l.vi();
                            if 0 < self.vars[vi].level {
                                self.an_seen[vi] = 1;
                            }
                        }
                    }
                }
                self.an_seen[vi] = 0;
            }
        }
    }
}

impl Solver {
    /// renamed from litRedundant
    fn analyze_removable(&mut self, l: Lit) -> bool {
        self.an_stack.clear();
        self.an_stack.push(l);
        let top = self.an_to_clear.len();
        while let Some(sl) = self.an_stack.pop() {
            // println!("analyze_removable.loop {:?}", self.an_stack);
            let ci = self.vars[sl.vi()].reason;
            if self.clauses[ci].lits.len() == 2 {
                let val = self.assigned(self.clauses[ci].lits[0]);
                if val == LFALSE {
                    self.clauses[ci].lits.swap(0, 1);
                }
            }
            for q in &self.clauses[ci].lits[1..] {
                let vi = q.vi();
                let lv = self.vars[vi].level;
                if self.an_seen[vi] != 1 && lv != 0 {
                    if self.vars[vi].reason != NULL_CLAUSE && self.an_level_map.contains(&lv) {
                        self.an_seen[vi] = 1;
                        self.an_stack.push(*q);
                        self.an_to_clear.push(*q);
                    } else {
                        for _ in top..self.an_to_clear.len() {
                            self.an_seen[self.an_to_clear.pop().unwrap().vi()] = 0;
                        }
                        return false;
                    }
                }
            }
        }
        true
    }
}

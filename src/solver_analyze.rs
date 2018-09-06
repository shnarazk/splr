use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause_manage::ClauseManagement;
use solver::Solver;
use types::*;
use var_manage::VarSelect;

pub trait CDCL {
    fn analyze(&mut self, confl: ClauseId) -> usize;
    fn analyze_final(&mut self, ci: ClauseId, skip_first: bool) -> ();
}

impl CDCL for Solver {
    fn analyze(&mut self, confl: ClauseId) -> usize {
        for mut l in &mut self.an_seen {
            debug_assert_eq!(*l, 0);
            // *l = 0;
        }
        // self.dump("analyze");
        self.an_learnt_lits.clear();
        self.an_learnt_lits.push(0);
        let dl = self.decision_level();
        let mut cid: usize = confl;
        let mut p = NULL_LIT;
        let mut ti = self.trail.len() - 1; // trail index
        let mut path_cnt = 0;
        loop {
            unsafe {
                let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()] as *mut Clause;
                // println!(
                //     "analyze({}): {} ({} :: {}) < {}",
                //     p.int(),
                //     *c,
                //     cid.to_kind(),
                //     cid.to_index(),
                //     self.cp[ClauseKind::Removable as usize].clauses.len()
                // );
                debug_assert_ne!(cid, NULL_CLAUSE);
                // println!("  analyze.loop {}", (*c));
                let d = (*c).rank;
                if cid.to_kind() == (ClauseKind::Removable as usize) {
                    self.bump_cid(cid);
                    let nblevel = self.lbd_of(&(*c).lits);
                    if nblevel + 1 < d {
                        (*c).rank = nblevel;
                        // if nblevel <= 30 {
                        //     (*c).just_used = true;
                        // }
                    }
                }
                // println!("{}を対応", (*c));
                //                'next_literal: for q in &(*c).lits {
                'next_literal: for i in 0..(*c).len() {
                    let q = lindex!(*c, i);
                    if q == p {
                        continue 'next_literal;
                    }
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
                            if self.vars[vi].reason != NULL_CLAUSE {
                                self.an_last_dl.push(q);
                            }
                        } else {
                            // println!("{} はレベル{}なので採用", q.int(), l);
                            self.an_learnt_lits.push(q);
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
                    let next_vi = p.vi();
                    cid = self.vars[next_vi].reason;
                    // println!("{} にフラグが立っている。この時path数は{}, そのreason {}を探索", next_vi, path_cnt - 1, cid);
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
        {
            self.an_level_map_key += 1;
            if 10_000_000 < self.an_level_map_key {
                self.an_level_map_key = 1;
            }
            for i in 1..n {
                let l = self.an_learnt_lits[i];
                self.an_to_clear.push(l);
                self.an_level_map[self.vars[l.vi()].level] = self.an_level_map_key;
            }
        }
        // println!("  analyze.loop 4 n = {}", n);
        let mut j = 1;
        for i in 1..n {
            let l = self.an_learnt_lits[i];
            if self.vars[l.vi()].reason == NULL_CLAUSE {
                self.an_learnt_lits[j] = l;
                j += 1;
            } else if !self.analyze_removable(l) {
                self.an_learnt_lits[j] = l;
                j += 1;
            }
        }
        self.an_learnt_lits.truncate(j);
        // glucose heuristics
        let r = self.an_learnt_lits.len();
        for i in 0..self.an_last_dl.len() {
            let l = self.an_last_dl[i];
            let vi = l.vi();
            let cid = self.vars[vi].reason;
            let len = self.cp[cid.to_kind()].clauses[cid.to_index()].lits.len();
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
        if self.an_learnt_lits.len() < 30 {
            self.minimize_with_bi_clauses();
        }
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
    fn analyze_final(&mut self, ci: ClauseId, skip_first: bool) -> () {
        self.conflicts.clear();
        if self.root_level != 0 {
            //for i in &self.clauses.iref(ci).lits[(if skip_first { 1 } else { 0 })..] {
            for i in (if skip_first { 1 } else { 0 })
                ..(self.cp[ci.to_kind()].clauses[ci.to_index()].len())
            {
                let l;
                match i {
                    0 => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lit[0],
                    1 => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lit[1],
                    _ => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lits[i - 2],
                }
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
                        for i in 1..(self.cp[ci.to_kind()].clauses[ci.to_index()].lits.len()) {
                            let l;
                            match i {
                                0 => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lit[1],
                                _ => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lits[i - 2],
                            }
                            // for l in &self.clauses.iref(ci).lits[1..]
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
        let key = self.an_level_map_key;
        while let Some(sl) = self.an_stack.pop() {
            // println!("analyze_removable.loop {:?}", self.an_stack);
            let cid = self.vars[sl.vi()].reason;
            let c0;
            let len;
            {
                let c = &self.cp[cid.to_kind()].clauses[cid.to_index()];
                c0 = c.lit[0];
                len = c.lits.len();
            }
            if len == 0 && self.assigned(c0) == LFALSE {
                self.cp[cid.to_kind()].clauses[cid.to_index()]
                    .lit
                    .swap(0, 1);
            }
            for i in 0..self.cp[cid.to_kind()].clauses[cid.to_index()].lits.len() + 1 {
                let q;
                match i {
                    0 => q = self.cp[cid.to_kind()].clauses[cid.to_index()].lit[1],
                    n => q = self.cp[cid.to_kind()].clauses[cid.to_index()].lits[n - 1],
                }
                let vi = q.vi();
                let lv = self.vars[vi].level;
                if self.an_seen[vi] != 1 && lv != 0 {
                    if self.vars[vi].reason != NULL_CLAUSE && self.an_level_map[lv as usize] == key
                    {
                        self.an_seen[vi] = 1;
                        self.an_stack.push(q);
                        self.an_to_clear.push(q);
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
    fn minimize_with_bi_clauses(&mut self) -> () {
        let len = self.an_learnt_lits.len();
        if 30 < len {
            return;
        }
        unsafe {
            let key = self.an_level_map_key;
            let vec = &mut self.an_learnt_lits as *mut Vec<Lit>;
            let nblevel = self.lbd_of(&*vec);
            if 6 < nblevel {
                return;
            }
            let l0 = self.an_learnt_lits[0];
            let p: Lit = l0.negate();
            for i in 1..len {
                self.mi_var_map[(*vec)[i].vi() as usize] = key;
            }
            let mut nb = 0;
            let mut cix = self.cp[ClauseKind::Binclause as usize].watcher[p as usize];
            while cix != NULL_CLAUSE {
                let c = &self.cp[ClauseKind::Binclause as usize].clauses[cix];
                let other = if c.lit[0] == p {
                    c.lit[1]
                } else {
                    c.lit[0]
                };
                let vi = other.vi();
                if self.mi_var_map[vi] == key && self.assigned(other) == LTRUE {
                    nb += 1;
                    self.mi_var_map[vi] -= 1;
                }
                cix = if c.lit[0] == p {
                    c.next_watcher[0]
                } else {
                    c.next_watcher[1]
                };
            }
            if 0 < nb {
                (*vec).retain(|l| *l == l0 || self.mi_var_map[l.vi()] == key);
            }
        }
    }
}

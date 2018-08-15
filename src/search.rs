use analyze::*;
use clause::*;
use clause_manage::ClauseManagement;
use restart::Restart;
use solver::*;
use std::cmp::max;
use types::*;
use var::VarOrdering;
use var_select::VarSelect;
use watch::*;

pub trait SolveSAT {
    /// returns `true` for SAT, `false` for UNSAT.
    fn search(&mut self) -> bool;
    fn propagate(&mut self) -> ClauseIndex;
    fn enqueue(&mut self, l: Lit, cid: ClauseIndex) -> bool;
    fn assume(&mut self, l: Lit) -> bool;
    fn cancel_until(&mut self, lv: usize) -> ();
}

impl SolveSAT for Solver {
    // adapt delayed update of watches
    fn propagate(&mut self) -> ClauseIndex {
        // println!("> propagate at {}", self.decision_level());
        while self.q_head < self.trail.len() {
            let p: Lit = self.trail[self.q_head];
            let p_usize: usize = p as usize;
            self.q_head += 1;
            self.stats[Stat::NumOfPropagation as usize] += 1;
            let wl = self.watches[p_usize].len();
            let false_lit = p.negate();
            'next_clause: for mut wi in 0..wl {
                // println!(" next_clause: {}", wi);
                unsafe {
                    let w = &mut self.watches[p_usize][wi] as *mut Watch;
                    debug_assert_ne!((*w).other, (*w).to);
                    // We use `Watch.to` to keep the literal which is the destination of propagation.
                    if (*w).other != 0 && self.assigned((*w).other) == LTRUE {
                        (*w).to = p;
                        continue 'next_clause;
                    }
                    let c = &mut self.clauses[(*w).by] as *mut Clause;
                    debug_assert!((*w).by == (*c).index, "A clause has an inconsistent index");
                    debug_assert!(false_lit == (*c).lits[0] || false_lit == (*c).lits[1]);
                    // Place the false literal at lits[1].
                    // And the last literal in unit clause will be at lits[0].
                    if (*c).lits[0] == false_lit {
                        (*c).lits.swap(0, 1);
                    }
                    let first = (*c).lits[0];
                    // debug_assert_eq!(false_lit, (*c).lits[1]);
                    let fv = self.assigned(first);
                    if fv == LTRUE {
                        // Satisfied by the other watch.
                        // Update watch with `other`, the cached literal
                        (*w).to = p;
                        continue 'next_clause;
                    }
                    (*w).other = first;
                    for k in 2..(*c).lits.len() {
                        let lk = (*c).lits[k];
                        if self.assigned(lk) != LFALSE {
                            (*c).tmp = k;
                            // Update the watch
                            (*w).to = lk.negate();
                            continue 'next_clause;
                        }
                    }
                    if fv == LFALSE {
                        // println!("  found a conflict variable {} by {}", first.vi(), (*c));
                        return (*w).by;
                    } else {
                        // println!("  unit propagation {} by {}", first.int(), (*c));
                        (*c).tmp = 1;
                        (*w).to = p;
                        debug_assert_eq!(first, (*c).lits[0]);
                        self.uncheck_enqueue(first, (*w).by);
                    }
                }
            }
            // No conflict: so let's move them!
            // use watches[0] to keep watches that don't move anywhere, temporally.
            // println!("  update watches");
            self.watches[0].clear();
            while let Some(w) = self.watches[p_usize].pop() {
                // debug_assert!(w.to != 0, "Invalid Watch.to found");
                if w.to == p {
                    self.watches[0].push(w)
                } else {
                    let ref mut c = &mut self.clauses[w.by];
                    c.lits.swap(1, c.tmp as usize);
                    self.watches[w.to as usize].push(w);
                }
            }
            debug_assert!(self.watches[p_usize].is_empty(), true);
            self.watches.swap(0, p_usize);
            // while let Some(w) = self.watches[0].pop() {
            //     // debug_assert!(w.to == p, "inconsistent propagation");
            //     self.watches[p_usize].push(w);
            // }
        }
        NULL_CLAUSE
    }
    fn search(&mut self) -> bool {
        // self.dump("search");
        let delta: f64 = (self.num_vars as f64).sqrt();
        let root_lv = self.root_level;
        loop {
            // self.dump("calling propagate");
            self.stats[Stat::NumOfPropagation as usize] += 1;
            let ci = self.propagate();
            let d = self.decision_level();
            // self.dump(format!("search called propagate and it returned {:?} at {}", ret, d));
            if ci == NULL_CLAUSE {
                // println!(" search loop enters a new level");
                let na = self.num_assigns();
                if na == self.num_vars {
                    return true;
                }
                if (self.max_learnts as usize) + na + self.fixed_len < self.clauses.len() {
                    self.reduce_database();
                } else if d == 0 && self.num_solved_vars < na {
                    self.simplify_database();
                    self.num_solved_vars = na;
                    self.rebuild_vh();
                }
                if !(self.q_head < self.trail.len()) {
                    let vi = self.select_var();
                    debug_assert_ne!(vi, 0);
                    let p = self.vars[vi].phase;
                    self.uncheck_assume(vi.lit(p));
                }
            } else {
                self.stats[Stat::NumOfBackjump as usize] += 1;
                if d == self.root_level {
                    self.analyze_final(ci, false);
                    return false;
                } else {
                    // self.dump(" before analyze");
                    let backtrack_level = self.analyze(ci);
                    // println!(" conflict analyzed {:?}", vec2int(v));
                    self.cancel_until(max(backtrack_level as usize, root_lv));
                    // println!(" backtracked to {}", backtrack_level);
                    let lbd;
                    if self.an_learnt_lits.len() == 1 {
                        let l = self.an_learnt_lits[0];
                        self.uncheck_enqueue(l, NULL_CLAUSE);
                        lbd = 1;
                    } else {
                        let v = self.an_learnt_lits.clone();
                        lbd = self.add_learnt(v);
                    }
                    self.decay_var_activity();
                    self.decay_cla_activity();
                    self.learnt_size_cnt -= 1;
                    if self.learnt_size_cnt == 0 {
                        let adj = 1.5 * self.learnt_size_adj;
                        self.learnt_size_adj = adj;
                        self.learnt_size_cnt = adj as u64;
                        self.max_learnts += delta;
                    }
                    if self.should_restart(lbd, d) {
                        self.cancel_until(root_lv);
                        println!("# Restart block: {}, force: {}", self.stats[Stat::NumOfBlockRestart as usize], self.stats[Stat::NumOfRestart as usize]);
                    }
                }
                // Since the conflict path pushes a new literal to trail, we don't need to pick up a literal here.
            }
        }
    }
    fn cancel_until(&mut self, lv: usize) -> () {
        let dl = self.decision_level();
        if dl <= lv {
            return;
        }
        let lim = self.trail_lim[lv];
        for l in &self.trail[lim..] {
            let vi = l.vi();
            {
                let v = &mut self.vars[vi];
                if v.level == dl {
                    v.phase = v.assign;
                }
                v.assign = BOTTOM;
                v.reason = NULL_CLAUSE;
            }
            self.var_order.insert(&self.vars, vi);
        }
        self.trail.truncate(lim); // FIXME
        self.trail_lim.truncate(lv);
        self.q_head = lim;
        // self.dump("cancel_until");
    }
    fn enqueue(&mut self, l: Lit, cid: ClauseIndex) -> bool {
        // println!("enqueue: {} by {}", l.int(), cid);
        let sig = l.lbool();
        let val = self.vars[l.vi()].assign;
        if val == BOTTOM {
            {
                let dl = self.decision_level();
                let v = &mut self.vars[l.vi()];
                v.assign = sig;
                v.level = dl;
                v.reason = cid;
            }
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }
    fn assume(&mut self, l: Lit) -> bool {
        self.trail_lim.push(self.trail.len());
        self.enqueue(l, NULL_CLAUSE)
    }
}

impl Solver {
    pub fn uncheck_enqueue(&mut self, l: Lit, ci: ClauseIndex) -> () {
        // if ci == NULL_CLAUSE {
        //     println!("uncheck_enqueue decide: {}", l.int());
        // } else {
        //     println!("uncheck_enqueue imply: {} by {}", l.int(), ci);
        // }
        debug_assert!(l != 0, "Null literal is about to be equeued");
        let dl = self.decision_level();
        let v = &mut self.vars[l.vi()];
        v.assign = l.lbool();
        v.level = dl;
        v.reason = ci;
        self.trail.push(l)
    }
    pub fn uncheck_assume(&mut self, l: Lit) -> () {
        let len = self.trail.len();
        self.trail_lim.push(len);
        self.uncheck_enqueue(l, NULL_CLAUSE);
    }
}

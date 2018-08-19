use clause::Clause;
use clause_manage::ClauseManagement;
use clause_manage::ClauseReference;
use solver::{Solver, Stat};
use solver_analyze::CDCL;
use solver_rollback::Restart;
use std::cmp::max;
use types::*;
use var_manage::VarSelect;

pub trait SolveSAT {
    /// returns `true` for SAT, `false` for UNSAT.
    fn search(&mut self) -> bool;
    fn propagate(&mut self) -> ClauseIndex;
    fn enqueue(&mut self, l: Lit, cid: ClauseIndex) -> bool;
    fn assume(&mut self, l: Lit) -> bool;
}

impl SolveSAT for Solver {
    fn propagate(&mut self) -> ClauseIndex {
        // println!("> propagate at {}", self.decision_level());
        while self.q_head < self.trail.len() {
            let p: Lit = self.trail[self.q_head];
            let p_usize: usize = p as usize;
            self.q_head += 1;
            self.stats[Stat::NumOfPropagation as usize] += 1;
            let false_lit = p.negate();
            'next_bi_clause: for mut wi in 0..self.bi_watches[p_usize].len() {
                // println!(" next_clause: {}", wi);
                unsafe {
                    let w = &mut self.bi_watches[p_usize][wi] as *mut Watch;
                    if (*w).by == NULL_CLAUSE {
                        (*w).to = NULL_LIT;
                        continue 'next_bi_clause;
                    }
                    debug_assert_ne!((*w).by, NULL_CLAUSE);
                    debug_assert_ne!((*w).other, 0);
                    // We use `Watch.to` to keep the literal which is the destination of propagation.
                    match self.assigned((*w).other) {
                        LFALSE => return (*w).by,
                        LTRUE => continue 'next_bi_clause,
                        _ => {
                            {
                                let mut cl = &mut self.clauses.mref((*w).by).lits;
                                if cl[0] == false_lit {
                                    cl.swap(0, 1);
                                }
                            }
                            self.uncheck_enqueue((*w).other, (*w).by);
                        }
                    }
                }
            }
            'next_clause: for mut wi in 0..self.watches[p_usize].len() {
                // println!(" next_clause: {}", wi);
                unsafe {
                    let w = &mut self.watches[p_usize][wi] as *mut Watch;
                    if (*w).by == NULL_CLAUSE {
                        (*w).to = NULL_LIT;
                        continue 'next_clause;
                    }
                    debug_assert_ne!((*w).other, (*w).to);
                    // We use `Watch.to` to keep the literal which is the destination of propagation.
                    if (*w).other != 0 && self.assigned((*w).other) == LTRUE {
                        (*w).to = p;
                        continue 'next_clause;
                    }
                    let c = self.clauses.mref((*w).by) as *mut Clause;
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
                        (*w).other = first;
                        continue 'next_clause;
                    }
                    for k in 2..(*c).lits.len() {
                        let lk = (*c).lits[k];
                        if self.assigned(lk) != LFALSE {
                            (*w).swap = k;
                            // Update the watch
                            (*w).to = lk.negate();
                            (*w).other = lk;
                            continue 'next_clause;
                        }
                    }
                    if fv == LFALSE {
                        // println!("  found a conflict variable {} by {}", first.vi(), (*c));
                        return (*w).by;
                    } else {
                        // println!("  unit propagation {} by {}", first.int(), (*c));
                        (*w).swap = 1;
                        (*w).to = p;
                        if (*w).other == (*c).lits[0] {
                            (*w).other = first;
                        }
                        self.uncheck_enqueue(first, (*w).by);
                    }
                }
            }
            // No conflict: so let's move them!
            // use watches[0] to keep watches that don't move anywhere, temporally.
            // println!("  update bi_watches");
            // self.bi_watches[0].clear();
            // while let Some(w) = self.bi_watches[p_usize].pop() {
            //     // debug_assert!(w.to != 0, "Invalid Watch.to found");
            //     if w.to == NULL_LIT {
            //         continue;
            //     } else if w.to == p {
            //             self.bi_watches[0].push(w);
            //     } else {
            //         self.clauses[w.by].lits.swap(1, w.swap as usize);
            //         self.bi_watches[w.to as usize].push(w);
            //     }
            // }
            // debug_assert!(self.bi_watches[p_usize].is_empty(), true);
            // self.bi_watches.swap(0, p_usize);
            // println!("  update watches");
            self.watches[0].clear();
            while let Some(w) = self.watches[p_usize].pop() {
                // debug_assert!(w.to != 0, "Invalid Watch.to found");
                if w.to == NULL_LIT {
                    continue;
                } else if w.to == p {
                    self.watches[0].push(w);
                } else {
                    self.clauses.mref(w.by).lits.swap(1, w.swap as usize);
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
                self.force_restart();
                if d == 0 && self.num_solved_vars < na {
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
                    // glucose reduction
                    let conflicts = self.stats[Stat::NumOfBackjump as usize] as usize;
                    if self.cur_restart * self.clauses.nb_clauses_before_reduce <= conflicts {
                        self.cur_restart = ((conflicts as f64)
                            / (self.clauses.nb_clauses_before_reduce as f64))
                            as usize + 1;
                        self.reduce_database();
                    }
                    self.block_restart(lbd, d);
                }
                // Since the conflict path pushes a new literal to trail, we don't need to pick up a literal here.
            }
        }
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
                self.clauses.mref(cid).locked = true;
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
        if 0 < ci {
            self.clauses.mref(ci).locked = true;
        }
        self.trail.push(l);
    }
    pub fn uncheck_assume(&mut self, l: Lit) -> () {
        self.trail_lim.push(self.trail.len());
        self.uncheck_enqueue(l, NULL_CLAUSE);
    }
}

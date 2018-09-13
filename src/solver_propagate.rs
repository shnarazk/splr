#![allow(unused_imports)]
use assign::Assignment;
use clause::{Clause, ClauseKind, ClauseIF};
use clause::ClauseManagement;
use clause::ClauseIdIndexEncoding;
use solver::{LBD, Solver, Stat};
use solver::SatSolver;
use solver_restart::Restart;
use std::cmp::max;
use types::*;
use var::HeapManagement;
use var::Satisfiability;
use clause::CheckPropagation;

/// for Solver
pub trait SolveSAT {
    /// returns `true` for SAT, `false` for UNSAT.
    fn search(&mut self) -> bool;
    fn propagate(&mut self) -> ClauseId;
    fn cancel_until(&mut self, lv: usize) -> ();
}

/// for Solver
trait CDCL {
    fn analyze(&mut self, confl: ClauseId) -> usize;
    fn analyze_final(&mut self, ci: ClauseId, skip_first: bool) -> ();
    fn analyze_removable(&mut self, l: Lit) -> bool;
    fn minimize_with_bi_clauses(&mut self) -> ();
}

impl SolveSAT for Solver {
    fn search(&mut self) -> bool {
        // self.dump("search");
        let root_lv = self.root_level;
        loop {
            // self.dump("calling propagate");
            self.stats[Stat::NumOfPropagation as usize] += 1;
            // for cp in &self.cp {
            //     if !cp.assertion_soundness() {
            //         println!("bjmp, rest, prpg, rdct, simp, {:?}", self.stats);
            //         panic!("fail assertion");
            //     }
            // }
            let ci = self.propagate();
            let d = self.am.decision_level();
            // self.dump(format!("search called propagate and it returned {:?} at {}", ret, d));
            if ci == NULL_CLAUSE {
                // println!(" search loop enters a new level");
                let na = self.num_assigns();
                if na == self.num_vars {
                    return true;
                }
                self.force_restart();
                if d == 0 && self.num_solved_vars < na {
                    self.cm.simplify(&mut self.cp, &self.assign);
                    self.stats[Stat::NumOfSimplification as usize] += 1;
                    self.progress("simp");
                    self.num_solved_vars = na;
                    self.var_order.rebuild(&self.assign, &self.vars);
                }
                if !(self.am.q_head < self.am.trail.len()) {
                    let vi = self.var_order.select_var(&self.assign, &self.vars);
                    debug_assert_ne!(vi, 0);
                    let sign = self.vars[vi].phase == LTRUE;
                    self.am.uncheck_assume(&mut self.assign, &mut self.vars[vi], vi.lit(sign as u8));
                }
            } else {
                self.stats[Stat::NumOfBackjump as usize] += 1;
                if d == self.root_level {
                    self.analyze_final(ci, false);
                    return false;
                } else {
                    // self.dump(" before analyze");
                    let backtrack_level = self.analyze(ci);
                    self.cancel_until(max(backtrack_level as usize, root_lv));
                    let lbd;
                    if self.an_learnt_lits.len() == 1 {
                        let l = self.an_learnt_lits[0];
                        self.am.uncheck_enqueue(&mut self.assign, &mut self.vars[l.vi()], l, NULL_CLAUSE);
                        lbd = 1;
                    } else {
                        unsafe {
                            let v = &mut self.an_learnt_lits as *mut Vec<Lit>;
                            lbd = self.add_learnt(&mut *v);
                        }
                    }
                    self.cm.decay_cla_activity();
                    // glucose reduction
                    let conflicts = self.stats[Stat::NumOfBackjump as usize] as usize;
                    if self.cur_restart * self.next_reduction <= conflicts {
                        self.cur_restart = (conflicts as f64 / self.next_reduction as f64) as usize + 1;
                        self.cm.reduce(&mut self.cp[ClauseKind::Removable as usize]);
                        self.next_reduction += self.cm.increment_step;
                        self.stats[Stat::NumOfReduction as usize] += 1;
                        self.progress("drop");
                    }
                    self.block_restart(lbd, d);
                }
                // Since the conflict path pushes a new literal to trail, we don't need to pick up a literal here.
            }
        }
    }

    fn propagate(&mut self) -> ClauseId {
        while self.am.q_head < self.am.trail.len() {
            let p: usize = self.am.trail[self.am.q_head] as usize;
            debug_assert!(1 < p);
            // self.cp[ClauseKind::Removable as usize].check_lit(&self.vars, "before propagation", p as Lit);
            self.am.q_head += 1;
            self.stats[Stat::NumOfPropagation as usize] += 1;
            for cs in &mut self.cp {
                let ret = cs.propagate(&mut self.assign, &mut self.vars, &mut self.am, p as Lit);
                if ret != NULL_CLAUSE {
                    return ret;
                }
            }
            // self.check_lit(ClauseKind::Removable, "after propagation", p as Lit);
        }
        NULL_CLAUSE
    }

    fn cancel_until(&mut self, lv: usize) -> () {
        if self.am.decision_level() <= lv {
            return;
        }
        let lim = self.am.trail_lim[lv];
        for l in &self.am.trail[lim..] {
            let vi = l.vi();
            {
                let v = &mut self.vars[vi];
                v.phase = self.assign[vi];
                self.assign[vi] = BOTTOM;
                if 0 < v.reason {
                    self.cp[v.reason.to_kind()].clauses[v.reason.to_index()].locked = false;
                }
                v.reason = NULL_CLAUSE;
            }
            self.var_order.insert(&self.vars, vi);
        }
        self.am.trail.truncate(lim); // FIXME
        self.am.trail_lim.truncate(lv);
        self.am.q_head = lim;
    }
}

impl CDCL for Solver {
    fn analyze(&mut self, confl: ClauseId) -> usize {
        self.an_learnt_lits.clear();
        self.an_learnt_lits.push(0);
        let dl = self.am.decision_level();
        let mut cid: usize = confl;
        let mut p = NULL_LIT;
        let mut ti = self.am.trail.len() - 1; // trail index
        let mut path_cnt = 0;
        loop {
            unsafe {
                let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()] as *mut Clause;
                debug_assert_ne!(cid, NULL_CLAUSE);
                if cid.to_kind() == ClauseKind::Removable as usize {
                    self.cm.bump(&mut self.cp, cid);
                    (*c).rank = (*c).lbd(&self.vars, &mut self.lbd_seen);
                    (*c).just_used = true;
                }
                'next_literal: for i in 0..(*c).len() {
                    let q = lindex!(*c, i);
                    if q == p {
                        continue 'next_literal;
                    }
                    let vi = q.vi();
                    let l = self.vars[vi].level;
                    debug_assert_ne!(self.assign[vi], BOTTOM);
                    if self.an_seen[vi] == 0 && 0 < l {
                        self.var_order.bump(&mut self.vars, vi, self.stats[Stat::NumOfBackjump as usize] as f64);
                        self.an_seen[vi] = 1;
                        if dl <= l {
                            path_cnt += 1;
                            if self.vars[vi].reason != NULL_CLAUSE {
                                self.an_last_dl.push(q);
                            }
                        } else {
                            self.an_learnt_lits.push(q);
                        }
                    }
                }
                // set the index of the next literal to ti
                while self.an_seen[self.am.trail[ti].vi()] == 0 {
                    ti -= 1;
                }
                p = self.am.trail[ti];
                {
                    let next_vi = p.vi();
                    cid = self.vars[next_vi].reason;
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
        // glucose heuristics
        let lbd = self.an_learnt_lits.lbd(&self.vars, &mut self.lbd_seen);
        while let Some(l) = self.an_last_dl.pop() {
            let vi = l.vi();
            let cid = self.vars[vi].reason;
            if self.cp[cid.to_kind()].clauses[cid.to_index()].rank < lbd {
                self.var_order.bump(&mut self.vars, vi, self.stats[Stat::NumOfBackjump as usize] as f64);
            }
        }
        for l in &self.an_to_clear {
            self.an_seen[l.vi()] = 0;
        }
        level_to_return
    }

    fn analyze_final(&mut self, ci: ClauseId, skip_first: bool) -> () {
        self.conflicts.clear();
        if self.root_level != 0 {
            let c = &self.cp[ci.to_kind()].clauses[ci.to_index()];
            for i in (if skip_first { 1 } else { 0 })..c.len() {
                let l = lindex!(c, i);
                let vi = l.vi();
                if 0 < self.vars[vi].level {
                    self.an_seen[vi] = 1;
                }
            }
            let tl0 = self.am.trail_lim[0];
            let start = if self.am.trail_lim.len() <= self.root_level {
                self.am.trail.len()
            } else {
                self.am.trail_lim[self.root_level]
            };
            for i in (tl0..start).rev() {
                let l: Lit = self.am.trail[i];
                let vi = l.vi();
                if self.an_seen[vi] == 1 {
                    if self.vars[vi].reason == NULL_CLAUSE {
                        self.conflicts.push(l.negate());
                    } else {
                        for i in 1..c.len() {
                            let l = lindex!(c, i);
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

    /// renamed from litRedundant
    fn analyze_removable(&mut self, l: Lit) -> bool {
        self.an_stack.clear();
        self.an_stack.push(l);
        let top = self.an_to_clear.len();
        let key = self.an_level_map_key;
        while let Some(sl) = self.an_stack.pop() {
            let cid = self.vars[sl.vi()].reason;
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            let len = c.len();
            if c.len() == 1 && (&self.assign[..]).assigned(c.lit[0]) == LFALSE {
                c.lit.swap(0, 1);
            }
            for i in 1..len {
                let q = lindex!(c, i);
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
            let nblevel = (*vec).lbd(&self.vars, &mut self.lbd_seen);            // let nblevel = self.lbd_vector(&*vec);
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
                if self.mi_var_map[vi] == key && (&self.assign[..]).assigned(other) == LTRUE {
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

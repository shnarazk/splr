use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseIndex;
use clause::ClauseKind;
use clause_manage::ClauseManagement;
use solver::{Solver, Stat};
use solver_analyze::CDCL;
use solver_rollback::Restart;
use std::cmp::max;
use types::*;
use var_manage::VarSelect;

pub trait SolveSAT {
    /// returns `true` for SAT, `false` for UNSAT.
    fn search(&mut self) -> bool;
    fn propagate(&mut self) -> ClauseId;
    fn enqueue(&mut self, l: Lit, cid: ClauseId) -> bool;
}

impl SolveSAT for Solver {
    fn propagate(&mut self) -> ClauseId {
        while self.q_head < self.trail.len() {
            let p: usize = self.trail[self.q_head] as usize;
            let false_lit = (p as Lit).negate();
            self.q_head += 1;
            self.stats[Stat::NumOfPropagation as usize] += 1;
            let kinds = [
                ClauseKind::Binclause,
                ClauseKind::Permanent,
                ClauseKind::Removable,
            ];
            let mut ci: ClauseIndex;
            for kind in &kinds {
                unsafe {
                    let ck = *kind as usize;
                    ci = self.cp[ck].watcher[p];
                    let mut tail = &mut self.cp[ck].watcher[p] as *mut usize;
                    *tail = NULL_CLAUSE;
                    'next_clause: while ci != NULL_CLAUSE {
                        let c = &mut self.cp[ck].clauses[ci] as *mut Clause;
                        if (*c).lit[0] == false_lit {
                            (*c).lit.swap(0, 1); // now my index is 1, others is 0.
                            (*c).next_watcher.swap(0, 1);
                        }
                        let next = (*c).next_watcher[1];
                        let first_value = self.assigned((*c).lit[0]);
                        if first_value != LTRUE {
                            for k in 0..(*c).lits.len() {
                                let lk = (*c).lits[k];
                                // below is equivalent to 'self.assigned(lk) != LFALSE'
                                if (((lk & 1) as u8) ^ self.vars[lk.vi()].assign) != 0 {
                                    (*c).lit[1] = lk;
                                    (*c).lits[k] = false_lit;
                                    (*c).next_watcher[1] =
                                        self.cp[ck].watcher[lk.negate() as usize];
                                    self.cp[ck].watcher[lk.negate() as usize] = ci;
                                    ci = next;
                                    continue 'next_clause;
                                }
                            }
                            if first_value == LFALSE {
                                *tail = ci;
                                return kind.id_from(ci);
                            } else {
                                self.uncheck_enqueue((*c).lit[0], kind.id_from(ci));
                            }
                        }
                        let watch = self.cp[ck].watcher[p];
                        if watch == 0 {
                            tail = &mut (*c).next_watcher[1];
                        }
                        (*c).next_watcher[1] = watch;
                        self.cp[ck].watcher[p] = ci;
                        ci = next;
                    }
                }
            }
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
                    self.cancel_until(max(backtrack_level as usize, root_lv));
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
                    if self.cur_restart * self.next_reduction <= conflicts {
                        self.cur_restart =
                            ((conflicts as f64) / (self.next_reduction as f64)) as usize + 1;
                        self.reduce_watchers();
                    }
                    self.block_restart(lbd, d);
                }
                // Since the conflict path pushes a new literal to trail, we don't need to pick up a literal here.
            }
        }
    }
    /// This function touches:
    ///  - vars
    ///  - trail
    fn enqueue(&mut self, l: Lit, cid: ClauseId) -> bool {
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
                mref!(self.cp, cid).locked = true;
            }
            // println!(
            //     "implication {} by {} {}",
            //     l.int(),
            //     cid.to_kind(),
            //     cid.to_index()
            // );
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }
}

impl Solver {
    /// This function touches:
    ///  - vars
    ///  - trail
    ///  - trail_lim
    pub fn uncheck_enqueue(&mut self, l: Lit, cid: ClauseId) -> () {
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
        v.reason = cid;
        mref!(self.cp, cid).locked = true;
        // if 0 < cid {
        //     println!(
        //         "::uncheck_enqueue of {} by {}::{}",
        //         l.int(),
        //         cid.to_kind(),
        //         cid.to_index(),
        //     );
        // }
        self.trail.push(l);
    }
    pub fn uncheck_assume(&mut self, l: Lit) -> () {
        self.trail_lim.push(self.trail.len());
        // println!("::decision {}", l.int());
        self.uncheck_enqueue(l, NULL_CLAUSE);
    }
}

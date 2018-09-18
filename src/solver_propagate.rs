use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseIndex;
use clause::ClauseKind;
use clause::ClauseFlag;
use clause::ClauseManagement;
use solver::{Solver, Stat};
use solver_analyze::CDCL;
use solver_rollback::Restart;
use std::cmp::max;
use types::*;
use var::Satisfiability;
use var_manage::VarSelect;

pub trait SolveSAT {
    /// returns `true` for SAT, `false` for UNSAT.
    fn search(&mut self) -> bool;
    fn propagate(&mut self) -> ClauseId;
    fn enqueue(&mut self, l: Lit, cid: ClauseId) -> bool;
}

impl SolveSAT for Solver {
    fn propagate(&mut self) -> ClauseId {
        let Solver {
            ref mut vars,
            ref mut cp,
            ref mut trail,
            ref trail_lim,
            ref mut q_head,
            ref mut stats,
            ..
        } = self;
        while *q_head < trail.len() {
            let p: usize = trail[*q_head] as usize;
            let false_lit = (p as Lit).negate();
            *q_head += 1;
            stats[Stat::NumOfPropagation as usize] += 1;
            let kinds = [
                ClauseKind::Binclause,
                ClauseKind::Permanent,
                ClauseKind::Removable,
            ];
            let mut ci: ClauseIndex;
            for kind in &kinds {
                unsafe {
                    let clauses = &mut cp[*kind as usize].clauses[..] as *mut [Clause];
                    let watcher = &mut cp[*kind as usize].watcher[..] as *mut [ClauseIndex];
                    ci = (*watcher)[p];
                    let mut tail = &mut (*watcher)[p] as *mut usize;
                    *tail = NULL_CLAUSE;
                    'next_clause: while ci != NULL_CLAUSE {
                        let c = &mut (*clauses)[ci] as *mut Clause;
                        if (*c).lit[0] == false_lit {
                            (*c).lit.swap(0, 1); // now my index is 1, others is 0.
                            (*c).next_watcher.swap(0, 1);
                        }
                        ci = (*c).next_watcher[1];
                        // let next = (*c).next_watcher[1];
                        let other = (*c).lit[0];
                        let other_value = vars.assigned(other);
                        if other_value != LTRUE {
                            for (k, lk) in (*c).lits.iter().enumerate() {
                                // below is equivalent to 'assigned(lk) != LFALSE'
                                if (((lk & 1) as u8) ^ vars[lk.vi()].assign) != 0 {
                                    let alt = &mut (*watcher)[lk.negate() as usize];
                                    (*c).next_watcher[1] = *alt;
                                    *alt = (*c).index;
                                    (*c).lit[1] = *lk;
                                    (*c).lits[k] = false_lit; // WARN: update this lastly (needed by enuremate)
                                    continue 'next_clause;
                                }
                            }
                            if other_value == LFALSE {
                                *tail = (*c).index;
                                return kind.id_from((*c).index);
                            } else {
                                // uncheck_enqueue(lit, kind.id_from((*c).index));
                                // uenqueue!(vars, trail, trail_lim, lit, kind.id_from((*c).index));
                                let dl = trail_lim.len();
                                let v = &mut vars[other.vi()];
                                v.assign = other.lbool();
                                v.level = dl;
                                v.reason = kind.id_from((*c).index);
                                trail.push(other);
                                (*c).set_flag(ClauseFlag::Locked, true);
                            }
                        }
                        let watch = (*watcher)[p];
                        if watch == 0 {
                            tail = &mut (*c).next_watcher[1];
                        }
                        (*c).next_watcher[1] = watch;
                        (*watcher)[p] = (*c).index;
                    }
                }
            }
        }
        NULL_CLAUSE
    }
    fn search(&mut self) -> bool {
        let root_lv = self.root_level;
        loop {
            self.stats[Stat::NumOfPropagation as usize] += 1;
            let ci = self.propagate();
            let d = self.decision_level();
            if ci == NULL_CLAUSE {
                let na = self.num_assigns();
                if na == self.num_vars {
                    return true;
                }
                self.force_restart();
                if d == 0 && self.num_solved_vars < na {
                    self.simplify();
                    self.num_solved_vars = na;
                    self.rebuild_vh();
                }
                if self.trail.len() <= self.q_head {
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
                    let backtrack_level = self.analyze(ci);
                    self.cancel_until(max(backtrack_level as usize, root_lv));
                    let lbd;
                    if self.an_learnt_lits.len() == 1 {
                        let l = self.an_learnt_lits[0];
                        self.uncheck_enqueue(l, NULL_CLAUSE);
                        lbd = 1;
                    } else {
                        unsafe {
                            let v = &mut self.an_learnt_lits as *mut Vec<Lit>;
                            lbd = self.add_learnt(&mut *v);
                        }
                    }
                    self.decay_var_activity();
                    self.decay_cla_activity();
                    // glucose reduction
                    let conflicts = self.stats[Stat::NumOfBackjump as usize] as usize;
                    if self.cur_restart * self.next_reduction <= conflicts {
                        self.cur_restart =
                            ((conflicts as f64) / (self.next_reduction as f64)) as usize + 1;
                        self.reduce();
                    }
                    self.block_restart(lbd, d);
                }
                // Since the conflict path pushes a new literal to trail, we don't need to pick up a literal here.
            }
        }
    }
    fn enqueue(&mut self, l: Lit, cid: ClauseId) -> bool {
        let sig = l.lbool();
        let val = self.vars[l.vi()].assign;
        if val == BOTTOM {
            {
                let dl = self.decision_level();
                let v = &mut self.vars[l.vi()];
                v.assign = sig;
                v.level = dl;
                v.reason = cid;
                mref!(self.cp, cid).set_flag(ClauseFlag::Locked, true);
            }
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }
}

impl Solver {
    pub fn uncheck_enqueue(&mut self, l: Lit, cid: ClauseId) -> () {
        debug_assert!(l != 0, "Null literal is about to be equeued");
        let dl = self.decision_level();
        let v = &mut self.vars[l.vi()];
        v.assign = l.lbool();
        v.level = dl;
        v.reason = cid;
        mref!(self.cp, cid).set_flag(ClauseFlag::Locked, true);
        self.trail.push(l);
    }
    pub fn uncheck_assume(&mut self, l: Lit) -> () {
        self.trail_lim.push(self.trail.len());
        self.uncheck_enqueue(l, NULL_CLAUSE);
    }
}

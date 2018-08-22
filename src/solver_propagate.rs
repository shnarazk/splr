use clause::Clause;
use clause::ClauseKind;
use clause::ClauseIdIndexEncoding;
use clause_manage::vec2int;
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
    fn propagate(&mut self) -> ClauseId;
    fn enqueue(&mut self, l: Lit, cid: ClauseId) -> bool;
    // fn assume(&mut self, l: Lit) -> bool;
}

impl SolveSAT for Solver {
    fn propagate(&mut self) -> ClauseId {
        while self.q_head < self.trail.len() {
            let p: Lit = self.trail[self.q_head];
            let false_lit = p.negate();
            let p_usize: usize = p as usize;
            self.q_head += 1;
            self.stats[Stat::NumOfPropagation as usize] += 1;
            // biclause
            let mut ci = self.clauses.watches_bi[p_usize];
            'next_bi_clauses: while ci != NULL_CLAUSE {
                let next;
                let other;
                unsafe {
                    let c =
                        &mut self.clauses.kind[ClauseKind::Permanent as usize][ci] as *mut Clause;
                    if (*c).lit[0] == false_lit {
                        other = (*c).lit[1];
                        next = (*c).next_watcher[0];
                    } else {
                        other = (*c).lit[0];
                        next = (*c).next_watcher[1]
                    };
                    if (*c).lit[0] == false_lit {
                        (*c).lit.swap(0, 1);
                        (*c).next_watcher.swap(0, 1);
                    }
                    println!(
                        " propagate bi clause: cix {}, false_lit {}, lit[0] {} = other {}, next {}",
                        ci,
                        false_lit.int(),
                        (*c).lit[0].int(),
                        other.int(),
                        next
                    );
                }
                match self.assigned(other) {
                    LFALSE => {
                        println!(" - confilct ix {} = id {}", ci, ci.as_permanent_id());
                        return ci.as_permanent_id();
                    }
                    LTRUE => {}
                    _ => {
                        println!(
                            " unit propagation {} by biclause ix {} = id {}",
                            other.int(),
                            ci,
                            ci.as_permanent_id()
                        );
                        self.uncheck_enqueue(other, ci.as_permanent_id());
                    }
                }
                ci = next;
            }
            // permanents
            ci = self.clauses.watches_per[p_usize];
            'next_permanent: while ci != NULL_CLAUSE {
                unsafe {
                    let c =
                        &mut self.clauses.kind[ClauseKind::Permanent as usize][ci] as *mut Clause;
                    let (other, next) = if (*c).lit[0] == false_lit {
                        ((*c).lit[1], (*c).next_watcher[0])
                    } else {
                        ((*c).lit[0], (*c).next_watcher[1])
                    };
                    if false {
                        println!(
                            " propagate permanent: {}, false_lit {}, lit[0] {} = other {}, next {}",
                            (*c),
                            false_lit.int(),
                            (*c).lit[0].int(),
                            other.int(),
                            next
                        );
                    }
                    debug_assert_ne!(other, false_lit);
                    debug_assert_ne!(other, NULL_LIT);
                    debug_assert!(!((*c).learnt));
                    (*c).swap = 0;
                    // Place the false literal at lit[1].
                    if (*c).lit[0] == false_lit {
                        (*c).lit.swap(0, 1);
                        (*c).next_watcher.swap(0, 1);
                    }
                    let fv = self.assigned(other);
                    if fv == LTRUE {
                        ci = next;
                        continue 'next_permanent;
                    }
                    if ci == 1 {
                        println!(
                            " - permanent: cix {}, false_lit {}, lit[{}, {}], lits {:?}",
                            ci,
                            false_lit.int(),
                            (*c).lit[0].int(),
                            (*c).lit[1].int(),
                            vec2int((*c).lits.clone())
                        );
                    }
                    let uni: Lit;
                    {
                        for k in 0..(*c).lits.len() {
                            let lk = (*c).lits[k];
                            if self.assigned(lk) != LFALSE {
                                (*c).swap = k + 1;
                                if ci == 1 {
                                    println!("   - found another: cix {}, false_lit {}, lit[{}, {}], lits {:?}", ci, false_lit.int(), (*c).lit[0].int(), (*c).lit[1].int(), vec2int((*c).lits.clone()));
                                }
                                ci = next;
                                continue 'next_permanent;
                            }
                        }
                        if fv == LFALSE {
                            println!(" - confilct ix {} = id {}", ci, ci.as_permanent_id());
                            return ci.as_permanent_id();
                        }
                        uni = (*c).lit[0];
                        debug_assert_eq!(fv, BOTTOM);
                        debug_assert_eq!(uni, other);
                        debug_assert_ne!(uni, p);
                        debug_assert_ne!(uni, false_lit);
                    }
                    self.uncheck_enqueue(uni, ci.as_permanent_id());
                    println!(
                        " unit propagation of {} by {} = id {} then {}",
                        other.int(),
                        (*c),
                        ci.as_permanent_id(),
                        next
                    );
                    ci = next;
                }
            }
            // deletables
            ci = self.clauses.watches_del[p_usize];
            'next_deletable: while ci != NULL_CLAUSE {
                unsafe {
                    let c =
                        &mut self.clauses.kind[ClauseKind::Deletable as usize][ci] as *mut Clause;
                    let (other, next) = if (*c).lit[0] == false_lit {
                        ((*c).lit[1], (*c).next_watcher[0])
                    } else {
                        ((*c).lit[0], (*c).next_watcher[1])
                    };
                    if ci == 1 {
                        println!(
                            "cix {}, false_lit {} watch {} other {}, next {}",
                            ci,
                            false_lit.int(),
                            (*c).lit[0].int(),
                            other.int(),
                            next
                        );
                    }
                    debug_assert_ne!(other, NULL_LIT);
                    (*c).swap = 0;
                    // Place the false literal at lit[1].
                    if (*c).lit[0] == false_lit {
                        (*c).lit.swap(0, 1);
                        (*c).next_watcher.swap(0, 1);
                    }
                    let fv = self.assigned(other);
                    if fv == LTRUE {
                        ci = next;
                        continue 'next_deletable;
                    }
                    let uni: Lit;
                    {
                        for k in 0..(*c).lits.len() {
                            let lk = (*c).lits[k];
                            if self.assigned(lk) != LFALSE {
                                (*c).swap = k + 1;
                                ci = next;
                                continue 'next_deletable;
                            }
                        }
                        if fv == LFALSE {
                            println!(" - confilct ix {} = id {}", ci, ci.as_deletable_id());
                            return ci.as_deletable_id();
                        }
                        uni = (*c).lit[0];
                    }
                    println!(
                        " unit propagation of {} by {} = id {}",
                        other.int(),
                        (*c),
                        ci.as_deletable_id()
                    );
                    self.uncheck_enqueue(uni, ci.as_deletable_id());
                    ci = next;
                }
            }
            let mut ci;
            // sweep binary clauses
            ci = self.clauses.watches_bi[p_usize];
            self.clauses.watches_bi[p_usize] = NULL_CLAUSE;
            while ci != NULL_CLAUSE {
                let c = &mut self.clauses.kind[ClauseKind::Permanent as usize][ci];
                let pivot = if (*c).lit[0] == false_lit { 0 } else { 1 };
                debug_assert_eq!(pivot, 1);
                let next = (*c).next_watcher[pivot];
                if 0 < c.swap {
                    let tmp = c.lit[pivot];
                    c.lit[pivot] = c.lits[c.swap - 1];
                    c.lits[c.swap - 1] = tmp;
                }
                let watch = (*c).lit[pivot].negate() as usize;
                let top = self.clauses.watches_bi[watch];
                c.next_watcher[pivot] = top;
                self.clauses.watches_bi[watch] = ci;
                ci = next;
            }
            // sweep permanent clauses
            ci = self.clauses.watches_per[p_usize];
            self.clauses.watches_per[p_usize] = NULL_CLAUSE;
            while ci != NULL_CLAUSE {
                let c = &mut self.clauses.kind[ClauseKind::Permanent as usize][ci];
                let pivot = if (*c).lit[0] == false_lit { 0 } else { 1 };
                debug_assert_eq!(pivot, 1);
                let next = (*c).next_watcher[pivot];
                if 0 < c.swap {
                    let tmp = c.lit[pivot];
                    c.lit[pivot] = c.lits[c.swap - 1];
                    c.lits[c.swap - 1] = tmp;
                }
                let watch = (*c).lit[pivot].negate() as usize;
                let top = self.clauses.watches_per[watch];
                c.next_watcher[pivot] = top;
                self.clauses.watches_per[watch] = ci;
                if false {
                    println!(
                        " move {} to {} connected to {}",
                        c,
                        (watch as u32).int(),
                        top
                    );
                }
                ci = next;
            }
            // sweep deletable clauses
            ci = self.clauses.watches_del[p_usize];
            self.clauses.watches_del[p_usize] = NULL_CLAUSE;
            while ci != NULL_CLAUSE {
                let c = &mut self.clauses.kind[ClauseKind::Deletable as usize][ci];
                let pivot = if (*c).lit[0] == false_lit { 0 } else { 1 };
                let next = (*c).next_watcher[pivot];
                if c.swap != 0 {
                    let tmp = c.lit[pivot];
                    c.lit[pivot] = c.lits[c.swap - 1];
                    c.lits[c.swap - 1] = tmp;
                }
                let watch = (*c).lit[pivot].negate() as usize;
                let top = self.clauses.watches_del[watch];
                c.next_watcher[pivot] = top;
                self.clauses.watches_del[watch] = ci;
                ci = next;
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
                    if self.cur_restart * self.clauses.next_reduction <= conflicts {
                        self.cur_restart = ((conflicts as f64)
                            / (self.clauses.next_reduction as f64))
                            as usize + 1;
                        self.reduce_database();
                    }
                    self.block_restart(lbd, d);
                }
                // Since the conflict path pushes a new literal to trail, we don't need to pick up a literal here.
            }
        }
    }
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
                self.clauses.mref(cid).locked = true;
            }
            println!("implication {} by {}", l.int(), cid.as_deletable_id());
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }
    //    fn assume(&mut self, l: Lit) -> bool {
    //        self.trail_lim.push(self.trail.len());
    //        self.enqueue(l, NULL_CLAUSE)
    //    }
}

impl Solver {
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
        if 0 < cid {
            self.clauses.mref(cid).locked = true;
        }
        println!(
            "uncheck implication {} by {}",
            l.int(),
            cid.as_deletable_id()
        );
        self.trail.push(l);
    }
    pub fn uncheck_assume(&mut self, l: Lit) -> () {
        self.trail_lim.push(self.trail.len());
        println!("decision {}", l.int());
        self.uncheck_enqueue(l, NULL_CLAUSE);
    }
}

#![allow(unreachable_code)]
use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause::ClausePack;
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use types::*;
use solver::SatSolver;
use var::Satisfiability;

// const DB_INIT_SIZE: usize = 1000;
const DB_INC_SIZE: usize = 50;
pub const KINDS: [ClauseKind; 3] = [
    ClauseKind::Removable,
    ClauseKind::Permanent,
    ClauseKind::Binclause,
];

pub trait ClauseManagement {
    fn bump_cid(&mut self, ci: ClauseId) -> ();
    fn decay_cla_activity(&mut self) -> ();
    fn reduce_watchers(&mut self) -> ();
    fn simplify_database(&mut self) -> bool;
    fn lbd_of(&mut self, v: &[Lit]) -> usize;
}

impl ClauseManagement for Solver {
    fn bump_cid(&mut self, cid: ClauseId) -> () {
        debug_assert_ne!(cid, 0);
        let a;
        {
            // let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            let c = mref!(self.cp, cid);
            a = c.activity + self.cla_inc;
            c.activity = a;
        }
        if 1.0e20 < a {
            for c in &mut self.cp[ClauseKind::Removable as usize].clauses {
                if c.learnt {
                    c.activity *= 1.0e-20;
                }
            }
            self.cla_inc *= 1.0e-20;
        }
    }
    fn decay_cla_activity(&mut self) -> () {
        self.cla_inc = self.cla_inc / self.config.clause_decay_rate;
    }
    /// 1. sort `permutation` which is a mapping: index -> ClauseIndex.
    /// 2. rebuild watches to pick up clauses which is placed in a good place in permutation.
    fn reduce_watchers(&mut self) -> () {
        {
            let ClausePack {
                ref mut clauses,
                ref mut permutation,
                ..
            } = &mut self.cp[ClauseKind::Removable as usize];
            // debug_assert_eq!(permutation.len(), clauses.len());
            permutation.retain(|i| !clauses[*i as usize].dead);
            // sort the range of 'permutation'
            permutation.sort_unstable_by(|&a, &b| clauses[a].cmp(&clauses[b]));
            let nc = permutation.len();
            let keep = if clauses[permutation[nc / 2]].rank <= 4 {
                3 * nc / 4
            } else {
                nc / 2
            };
            for i in keep + 1..nc {
                let mut c = &mut clauses[permutation[i]];
                if !c.locked && !c.just_used {
                    c.dead = true;
                }
            }
            // permutation.retain(|&i| clauses[i].index != DEAD_CLAUSE);
        }
        // self.garbage_collect(ClauseKind::Removable);
        self.next_reduction += DB_INC_SIZE + (self.c_lvl.0 as usize);
        self.stats[Stat::NumOfReduction as usize] += 1;
        self.progress("drop");
    }
    fn simplify_database(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        for ck in &KINDS {
            for ci in 1..self.cp[*ck as usize].clauses.len() {
                unsafe {
                    let c = &mut self.cp[*ck as usize].clauses[ci] as *mut Clause;
                    if self.vars.satisfies(&*c) {
                        // There's no locked clause.
                        (*c).dead = true;
                    } else if false {
                        // TODO implement Clause::is_unit_clause()
                        if !self.enqueue((*c).lits[0], NULL_CLAUSE) {
                            self.ok = false;
                        }
                        (*c).dead = true;
                    } else if self.eliminator.use_elim && *ck == ClauseKind::Removable {
                        for i in 0..(*c).len() {
                            let l = lindex!((*c), i);
                            if self.vars[l.vi()].eliminated {
                                (*c).dead = true;
                                break;
                            }
                        }
                    }
                }
            }
        }
        self.stats[Stat::NumOfSimplification as usize] += 1;
        if self.eliminator.use_elim && self.stats[Stat::NumOfSimplification as usize] % 8 == 0 {
            self.eliminate();
        }
        for ck in &KINDS {
            self.garbage_collect(*ck);
        }
        self.progress("simp");
        true
    }
    fn lbd_of(&mut self, v: &[Lit]) -> usize {
        let key_old = self.lbd_seen[0];
        let key = if 10_000_000 < key_old { 1 } else { key_old + 1 };
        let mut cnt = 0;
        for l in v {
            let lv = &mut self.lbd_seen[self.vars[l.vi()].level];
            if *lv != key {
                *lv = key;
                cnt += 1;
            }
        }
        self.lbd_seen[0] = key;
        cnt
    }
}

impl Solver {
    fn garbage_collect(&mut self, kind: ClauseKind) -> () {
        if self.cp[kind as usize].watcher[1] == NULL_CLAUSE {
            return;
        }
        let mut ci = self.cp[kind as usize].watcher[1];
        while ci != NULL_CLAUSE {
            let c = &self.cp[kind as usize].clauses[ci];
            debug_assert!(c.dead);
            debug_assert!(c.lit[0] == NULL_LIT || c.lit[1] == NULL_LIT);
            let index = (c.lit[0] != NULL_LIT) as usize;
            ci = c.next_watcher[index];
        }
        unsafe {
            let garbage = &mut self.cp[kind as usize].watcher[1] as *mut ClauseId;
            // println!("garbage start: {}", self.cp[kind as usize].watcher[0]);
            for l in 2..self.vars.len()*2 {
                let vi = (l as Lit).vi();
                let mut pri = &mut self.cp[kind as usize].watcher[l] as *mut ClauseId;
                let mut ci = self.cp[kind as usize].watcher[l];
                'next_clause: while ci != NULL_CLAUSE {
                    let c = &mut self.cp[kind as usize].clauses[ci] as *mut Clause;
                    if !(*c).dead {
                        debug_assert!(!(*c).dead);
                        if (*c).lit[0].vi() == vi {
                            ci = (*c).next_watcher[0];
                            pri = &mut (*c).next_watcher[0];
                        } else {
                            ci = (*c).next_watcher[1];
                            pri = &mut (*c).next_watcher[1];
                        }
                        continue;
                    }
                    debug_assert!((*c).dead);
                    if (*c).lit[0] == NULL_LIT && (*c).lit[1] == NULL_LIT {
                        panic!("not be");
                        let me = ci;
                        ci = (*c).next_watcher[0];
                        *pri = (*c).next_watcher[0];
                        (*c).next_watcher[0] = *garbage;
                        (*c).next_watcher[1] = *garbage;
                        *garbage = me;
                        assert!((*c).lit[0] == NULL_LIT || (*c).lit[1] == NULL_LIT);
                    } else if (*c).lit[0].vi() == vi {
                        (*c).lit[0] = NULL_LIT;
                        let me = ci;
                        ci = (*c).next_watcher[0];
                        *pri = (*c).next_watcher[0];
                        if (*c).lit[1] != NULL_LIT {
                            (*c).next_watcher[0] = *garbage;
                            *garbage = me;
                        } else {
                            (*c).next_watcher[0] = (*c).next_watcher[1];
                        }
                        assert!((*c).lit[0] == NULL_LIT || (*c).lit[1] == NULL_LIT);
                    } else {
                        (*c).lit[1] = NULL_LIT;
                        let me = ci;
                        ci = (*c).next_watcher[1];
                        *pri = (*c).next_watcher[1];
                        if (*c).lit[0] != NULL_LIT {
                            (*c).next_watcher[1] = *garbage;
                            *garbage = me;
                        } else {
                            (*c).next_watcher[1] = (*c).next_watcher[0];
                        }
                        assert!((*c).lit[0] == NULL_LIT || (*c).lit[1] == NULL_LIT);
                    }
                }
            }
            // recycle garbages
            let recycled = &mut self.cp[kind as usize].watcher[0] as *mut ClauseId;
            let mut pri = &mut self.cp[kind as usize].watcher[1] as *mut ClauseId;
            let mut ci = self.cp[kind as usize].watcher[1];
            while ci != NULL_CLAUSE {
                let c = &mut self.cp[kind as usize].clauses[ci] as *mut Clause;
                if !(*c).dead {
                    panic!("not dead {:?}", *c);
                }
                debug_assert!((*c).dead);
                if (*c).lit[0] == NULL_LIT && (*c).lit[1] == NULL_LIT {
                    ci = (*c).next_watcher[0];
                    *pri = (*c).next_watcher[0];
                    (*c).next_watcher[0] = *recycled;
                    (*c).next_watcher[1] = *recycled;
                    *recycled = (*c).next_watcher[0];
                    (*c).dead = false;
                    // println!("recycle{} {} w1{}, w2{}", (*c).index, (*c), (*c).next_watcher[0], (*c).next_watcher[1]);
                } else {
                    let index = ((*c).lit[0] != NULL_LIT) as usize; // the other might have still active path
                    ci = (*c).next_watcher[index];
                    pri = &mut (*c).next_watcher[index];
                }
            }
        }
        debug_assert_eq!(self.cp[kind as usize].watcher[1], NULL_CLAUSE);
    }
    // print a progress report
    fn progress(&self, mes: &str) -> () {
        let nv = self.vars.len() - 1;
        let k = if self.trail_lim.is_empty() {
            self.trail.len()
        } else {
            self.trail_lim[0]
        };
        let sum = k + self.eliminator.eliminated_vars;
        let deads = self.cp[ClauseKind::Removable as usize].clauses.iter().filter(|c| c.dead).count();
        let cnt = self.cp[ClauseKind::Removable as usize].clauses.iter().filter(|c| c.rank <= 2).count();
        println!(
            "#{}, DB:R|P|B, {:>8}({:>8}, {:>8}), {:>8}, {:>5}, Progress: {:>6}+{:>6}({:>7.3}%), Restart:b|f, {:>6}, {:>6}, EMA:a|l, {:>5.2}, {:>6.2}, LBD: {:>6.2}",
            mes,
            self.cp[ClauseKind::Removable as usize].clauses.len() - 1,
            cnt,
            deads,
            self.cp[ClauseKind::Permanent as usize].clauses.len() - 1,
            self.cp[ClauseKind::Binclause as usize].clauses.len() - 1,
            k,
            self.eliminator.eliminated_vars,
            (sum as f32) / (nv as f32) * 100.0,
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
            self.ema_asg.get(),
            self.ema_lbd.get(),
            self.ema_lbd.fast,
        );
    }
}

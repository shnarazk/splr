use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause::ClausePack;
use clause::DEAD_CLAUSE;
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
            debug_assert_eq!(permutation.len(), clauses.len());
            // sort the range of 'permutation'
            permutation[1..].sort_by(|&a, &b| clauses[a].cmp(&clauses[b]));
            let nc = permutation.len();
            let keep = if clauses[permutation[nc / 2]].rank <= 4 {
                3 * nc / 4
            } else {
                nc / 2
            };
            for i in keep + 1..nc {
                let mut c = &mut clauses[permutation[i]];
                if !c.locked && !c.just_used {
                    c.index = DEAD_CLAUSE;
                }
            }
            permutation.retain(|&i| clauses[i].index != DEAD_CLAUSE);
        }
        self.garbage_collect(ClauseKind::Removable);
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
                    if self.satisfies(&*c) {
                        // There's no locked clause.
                        (*c).index = DEAD_CLAUSE;
                    } else if false {
                        // TODO  implement Clause::is_unit_clause()
                        if !self.enqueue((*c).lits[0], NULL_CLAUSE) {
                            self.ok = false;
                        }
                        (*c).index = DEAD_CLAUSE;
                    } else if self.eliminator.use_elim && *ck == ClauseKind::Removable {
                        for i in 0..(*c).len() {
                            let l = lindex!((*c), i);
                            if self.vars[l.vi()].eliminated {
                                (*c).index = DEAD_CLAUSE;
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
    // # Prerequisite
    /// - `ClausePack.clauses` has dead clauses, and their index fields hold valid vaule.
    /// - `Caluse.index` of all the dead clauses is DEAD_CLAUSE.
    /// - `ClausePack.permutation` is valid and can be destoried here.
    ///
    /// # Result
    /// - `ClausePack.clauses` has only active clauses, and their sorted with new index.
    /// - `ClausePack.permutation` is sorted.
    /// - `Var.reason` is updated with new clause ids.
    /// - By calling `rebuild_watchers`, All `ClausePack.watcher` hold valid links.
    fn garbage_collect(&mut self, kind: ClauseKind) -> () {
        let dl = self.decision_level();
        {
            let ClausePack {
                ref mut clauses,
                ref mut permutation,
                ..
            } = &mut self.cp[kind as usize];
            // set new indexes to index field of active clauses.
            let mut ni = 0; // new index
            for c in &mut *clauses {
                if c.index != DEAD_CLAUSE {
                    c.index = ni;
                    ni += 1;
                }
            }
            // rebuild reason
            if dl == 0 {
                for v in &mut self.vars[1..] {
                    v.reason = NULL_CLAUSE;
                }
            } else {
                for v in &mut self.vars[1..] {
                    let cid = v.reason;
                    if cid.to_kind() == kind as usize {
                        v.reason = kind.id_from(clauses[cid].index);
                    }
                }
            }
            // GC
            clauses.retain(|ref c| c.index != DEAD_CLAUSE);
            // rebuild permutation
            permutation.clear();
            for i in 0..clauses.len() {
                debug_assert_eq!(clauses[i].index, i);
                permutation.push(i);
            }
        }
        self.rebuild_watchers(kind);
    }
    pub fn rebuild_watchers(&mut self, kind: ClauseKind) -> () {
        let ClausePack {
            ref mut clauses,
            ref mut watcher,
            ..
        } = &mut self.cp[kind as usize];
        for mut x in &mut *watcher {
            *x = NULL_CLAUSE;
        }
        for mut c in &mut *clauses {
            if c.index == DEAD_CLAUSE {
                continue;
            }
            let w0 = c.lit[0].negate() as usize;
            c.next_watcher[0] = watcher[w0];
            watcher[w0] = c.index;
            let w1 = c.lit[1].negate() as usize;
            c.next_watcher[1] = watcher[w1];
            watcher[w1] = c.index;
        }
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
        let cnt = self.cp[ClauseKind::Removable as usize].clauses.iter().filter(|c| c.rank <= 2).count();
        println!(
            "#{}, DB:R|P|B, {:>8}({:>8}), {:>8}, {:>5}, Progress: {:>6}+{:>6}({:>7.3}%), Restart:b|f, {:>6}, {:>6}, EMA:a|l, {:>5.2}, {:>6.2}, LBD: {:>6.2}",
            mes,
            self.cp[ClauseKind::Removable as usize].clauses.len() - 1,
            cnt,
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

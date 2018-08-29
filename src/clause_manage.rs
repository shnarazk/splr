use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause::ClausePack;
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use std::usize::MAX;
use types::*;

const DB_INIT_SIZE: usize = 1000;
const DB_INC_SIZE: usize = 50;
const KINDS: [ClauseKind; 3] = [
    ClauseKind::Binclause,
    ClauseKind::Permanent,
    ClauseKind::Removable,
];

pub trait ClauseManagement {
    fn bump_cid(&mut self, ci: ClauseId) -> ();
    fn decay_cla_activity(&mut self) -> ();
    fn add_clause(&mut self, v: Vec<Lit>) -> bool;
    fn add_learnt(&mut self, v: Vec<Lit>) -> usize;
    fn reduce_watchers(&mut self) -> ();
    fn simplify_database(&mut self) -> bool;
    fn drain_unless<F>(&mut self, f: &F) -> bool
    where
        F: Fn(&Clause) -> bool;
    fn lbd_of(&mut self, v: &[Lit]) -> usize;
}

impl ClauseManagement for Solver {
    #[inline]
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
    // renamed from clause_new
    fn add_clause(&mut self, mut v: Vec<Lit>) -> bool {
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means totology.
        for i in 0..v.len() {
            let li = v[i];
            let sat = self.assigned(li);
            if sat == LTRUE || li.negate() == l_ {
                return true;
            } else if sat != LFALSE && li != l_ {
                v[j] = li;
                j += 1;
                l_ = li;
            }
        }
        v.truncate(j);
        let kind = if v.len() == 2 {
            ClauseKind::Binclause
        } else {
            ClauseKind::Permanent
        };
        match v.len() {
            0 => true,
            1 => self.enqueue(v[0], NULL_CLAUSE),
            _ => {
                self.attach_clause(Clause::new(kind, false, 0, v));
                true
            }
        }
    }
    /// renamed from newLearntClause
    fn add_learnt(&mut self, mut v: Vec<Lit>) -> usize {
        if v.len() == 1 {
            self.uncheck_enqueue(v[0], NULL_CLAUSE);
            0;
        }
        let lbd;
        if v.len() == 2 {
            lbd = 0;
        } else {
            lbd = self.lbd_of(&v);
        }
        let mut i_max = 0;
        let mut lv_max = 0;
        // seek a literal with max level
        for i in 0..v.len() {
            let vi = v[i].vi();
            let lv = self.vars[vi].level;
            if self.vars[vi].assign != BOTTOM && lv_max < lv {
                i_max = i;
                lv_max = lv;
            }
        }
        v.swap(1, i_max);
        let l0 = v[0];
        let kind = if v.len() == 2 {
            ClauseKind::Binclause
        } else {
            ClauseKind::Removable
        };
        let cid = self.attach_clause(Clause::new(kind, true, lbd, v));
        self.bump_cid(cid);
        self.uncheck_enqueue(l0, cid);
        lbd
    }
    /// 1. sort `permutation` which is a mapping: index -> ClauseIndex.
    /// 2. rebuild watches to pick up clauses which is placed in a good place in permutation.
    fn reduce_watchers(&mut self) -> () {
        {
            let ClausePack {
                ref mut clauses,
                ref mut watcher,
                ref mut permutation,
                ..
            } = &mut self.cp[ClauseKind::Removable as usize];
            // sort the range of 'permutation'
            permutation[1..].sort_by(|&a, &b| clauses[a].cmp(&clauses[b]));
            let nc = permutation.len();
            for i in nc / 2..nc {
                let mut c = &mut clauses[permutation[i]];
                if !c.locked && !c.just_used {
                    c.frozen = true;
                }
            }
            permutation.retain(|&i| !clauses[i].frozen);
            // rebuild watches
            for mut x in &mut *watcher {
                *x = NULL_CLAUSE;
            }
            for mut c in clauses {
                if c.frozen {
                    continue;
                }
                let w0 = c.lit[0].negate() as usize;
                c.next_watcher[0] = watcher[w0];
                watcher[w0] = c.index;
                let w1 = c.lit[1].negate() as usize;
                c.next_watcher[1] = watcher[w1];
                watcher[w1] = c.index;
            }
            self.next_reduction += DB_INC_SIZE + (self.c_lvl.0 as usize);
            self.stats[Stat::NumOfReduction as usize] += 1;
        }
        self.progress("drop 1/2");
    }
    fn simplify_database(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        // remove unsatisfiable literals in clauses
        let targets: Vec<Lit> = self.trail[self.num_solved_vars..]
            .iter()
            .map(|l| l.negate())
            .collect();
        // clear the reasons of variables satisfied at level zero.
        for l in &self.trail {
            self.vars[l.vi() as usize].reason = NULL_CLAUSE;
        }
        let thr = (self.ema_lbd.fast / 2.0) as usize;
        println!("thr {}",  thr);
        for ck in &KINDS {
            for mut c in &mut self.cp[*ck as usize].clauses {
                if !(*c).frozen {
                    c.lits.retain(|l| {
                        for t in &targets {
                            if t == l {
                                return false;
                            }
                        }
                        true
                    });
                }
            }
            // set key FIXME check lit[2] and lits[..]
            // let thr = self.cp[*ck as usize].clauses[self.cp[*ck as usize].permutation[self.cp[*ck as usize].permutation.len() -1]].len() / 2;
            for ci in 1..self.cp[*ck as usize].clauses.len() {
                unsafe {
                    let c = &mut self.cp[*ck as usize].clauses[ci] as *mut Clause;
                    if ((*c).frozen && thr <= (*c).len()) || self.satisfies(&*c) {
                        (*c).index = MAX;
                    } else if (*c).lits.len() == 0 && false {
                        if !self.enqueue((*c).lits[0], NULL_CLAUSE) {
                            self.ok = false;
                        }
                        (*c).index = MAX;
                        // } else {
                        //     let new = self.lbd_of(&(*c).lits);
                        //     if new < (*c).rank {
                        //         (*c).rank = new;
                        //     }
                        // }
                    }
                    (*c).frozen = false;
                }
            }
        // self.eliminate(true);
            let ClausePack {
                ref mut clauses,
                ref mut watcher,
                ref mut permutation,
                ..
            } = &mut self.cp[*ck as usize];
            let n = clauses.len();
            clauses.retain(|ref c| c.index < MAX);
            let len = clauses.len();
            if n == len {
                continue;
            }
            permutation.clear();
            for i in 0..len {
                clauses[i].index = i;
                permutation.push(i);
            }
            // rebuild watches for deletabl es
            for mut x in &mut *watcher {
                *x = NULL_CLAUSE;
            }
            for mut c in &mut *clauses {
                let w0 = c.lit[0].negate() as usize;
                c.next_watcher[0] = watcher[w0];
                watcher[w0] = c.index;
                let w1 = c.lit[1].negate() as usize;
                c.next_watcher[1] = watcher[w1];
                watcher[w1] = c.index;
            }
        }
        self.progress("simplify");
        true
    }
    fn drain_unless<F>(&mut self, cond: &F) -> bool
    where
        F: Fn(&Clause) -> bool,
    {
        // extend permutation table if needed
        for ck in &KINDS {
            let nc = self.cp[*ck as usize].clauses.len();
            let perm = &mut self.cp[*ck as usize].permutation;
            if perm.len() < nc {
                unsafe {
                    perm.reserve(nc);
                    perm.set_len(nc);
                }
            }
            // reinitialize the permutation table.
            for x in perm {
                *x = 0;
            }
        }
        // clear the reasons of variables satisfied at level zero.
        for l in &self.trail {
            self.vars[l.vi() as usize].reason = NULL_CLAUSE;
        }
        for ck in &KINDS {
            self.cp[*ck as usize].clauses.retain(cond);
            let len = self.cp[*ck as usize].clauses.len();
            let perm = &mut self.cp[*ck as usize].permutation;
            for i in 0..len {
                let old: usize = self.cp[*ck as usize].clauses[i].index;
                perm[old] = i;
                self.cp[*ck as usize].clauses[i].index = i;
            }
            self.cp[*ck as usize].clauses.truncate(len);
            // rebuild watches for deletables
            for mut x in &mut self.cp[*ck as usize].watcher {
                *x = NULL_CLAUSE;
            }
            for mut c in &mut self.cp[*ck as usize].clauses {
                let w0 = c.lit[0].negate() as usize;
                c.next_watcher[0] = self.cp[*ck as usize].watcher[w0];
                self.cp[*ck as usize].watcher[w0] = c.index;
                let w1 = c.lit[1].negate() as usize;
                c.next_watcher[1] = self.cp[*ck as usize].watcher[w1];
                self.cp[*ck as usize].watcher[w1] = c.index;
            }
        }
        true
    }
    fn lbd_of(&mut self, v: &[Lit]) -> usize {
        let key;
        let key_old = self.lbd_seen[0];
        if 10_000_000 < key_old {
            key = 1;
        } else {
            key = key_old + 1;
        }
        self.lbd_seen[0] = key;
        let mut cnt = 0;
        for l in v {
            let lv = self.vars[l.vi()].level;
            if self.lbd_seen[lv] != key && lv != 0 {
                self.lbd_seen[lv] = key;
                cnt += 1;
            }
        }
        if cnt == 0 {
            1
        } else {
            cnt
        }
    }
}

impl Solver {
    // print a progress report
    fn progress(&self, mes: &str) -> () {
        println!(
            "#{}, DB:R|P|B, {:>9}({:>9}), {:>8}, {:>5}, Restart:b|f, {:>6}, {:>6}, EMA:a|l, {:>6.2}, {:>6.2}",
            mes,
            self.cp[ClauseKind::Removable as usize].permutation.len() - 1,
            self.cp[ClauseKind::Removable as usize].clauses.len() - 1,
            self.cp[ClauseKind::Permanent as usize].clauses.len() - 1,
            self.cp[ClauseKind::Binclause as usize].clauses.len() - 1,
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
            self.ema_asg.get(),
            self.ema_lbd.get(),
        );
    }
}

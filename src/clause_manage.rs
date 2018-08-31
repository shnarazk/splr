use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause::ClausePack;
use clause::DEAD_CLAUSE;
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use types::*;

// const DB_INIT_SIZE: usize = 1000;
const DB_INC_SIZE: usize = 50;
pub const KINDS: [ClauseKind; 3] = [
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
                    c.index = DEAD_CLAUSE;
                }
            }
            permutation.retain(|&i| !clauses[i].frozen);
        }
        self.garbage_collect(ClauseKind::Removable); // too many clauses
        // if 6 * self.cp[ClauseKind::Removable as usize].permutation.len()
        //     < self.cp[ClauseKind::Removable as usize].clauses.len()
        // {
        //     self.garbage_collect(ClauseKind::Removable); // too many clauses
        // } else {
        //     self.rebuild_watchers(ClauseKind::Removable);
        // }
        self.next_reduction += DB_INC_SIZE + (self.c_lvl.0 as usize);
        self.stats[Stat::NumOfReduction as usize] += 1;
        self.progress("drop");
    }
    fn simplify_database(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        // remove unsatisfiable literals in clauses
        let targets: Vec<Lit> = self.trail[self.num_solved_vars..]
            .iter()
            .map(|l| l.negate())
            .collect();
        for ck in &KINDS {
            debug_assert_eq!(self.cp[*ck as usize].clauses[0].index, 0);
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
            let thr = (self.ema_lbd.slow / 2.0) as usize;
            for ci in 1..self.cp[*ck as usize].clauses.len() {
                unsafe {
                    let c = &mut self.cp[*ck as usize].clauses[ci] as *mut Clause;
                    if ((*c).frozen && thr < (*c).len()) || self.satisfies(&*c) {
                        (*c).index = DEAD_CLAUSE;
                    } else if (*c).lits.len() == 0 && false {
                        if !self.enqueue((*c).lits[0], NULL_CLAUSE) {
                            self.ok = false;
                        }
                        (*c).index = DEAD_CLAUSE;
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
            if self.cp[ClauseKind::Permanent as usize].clauses.len() < 1_000_000 {
                self.eliminate(true);
            }
            self.garbage_collect(*ck);
        }
        self.progress("simp");
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
                    if 0 < cid && cid.to_kind() == kind as usize {
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
            if c.frozen || c.index == DEAD_CLAUSE {
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
        let k = if self.trail_lim.is_empty() { self.trail.len() } else { self.trail_lim[0] };
        println!(
            "#{}, DB:R|P|B, {:>8}({:>8}), {:>8}, {:>5}, Progress: {:>6}({:>4.1}%), Restart:b|f, {:>6}, {:>6}, EMA:a|l, {:>5.2}, {:>5.2}, LBD: {:>5.2}",
            mes,
            self.cp[ClauseKind::Removable as usize].permutation.len() - 1,
            self.cp[ClauseKind::Removable as usize].clauses.len() - 1,
            self.cp[ClauseKind::Permanent as usize].clauses.len() - 1,
            self.cp[ClauseKind::Binclause as usize].clauses.len() - 1,
            k,
            (k as f32) / (nv as f32),
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
            self.ema_asg.get(),
            self.ema_lbd.get(),
            self.ema_lbd.fast,
        );
    }
}

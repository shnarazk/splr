use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
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
    fn reduce_database(&mut self) -> ();
    fn simplify_database(&mut self) -> ();
    fn lbd_of(&mut self, v: &[Lit]) -> usize;
}

#[derive(Debug)]
pub struct ClauseMap {
    pub init_size_of_permanents: usize,
    pub next_reduction: usize,
    pub kind: [Vec<Clause>; 2],
    pub watches_per: Vec<ClauseId>,
    pub watches_del: Vec<ClauseId>,
    pub watches_bi: Vec<ClauseId>,
    permutation_per: Vec<ClauseId>,
    permutation_del: Vec<ClauseId>,
}

impl ClauseMap {
    pub fn new(nv: usize, nc: usize) -> ClauseMap {
        let mut k = [Vec::with_capacity(nc + 1), Vec::with_capacity(nc + 1)];
        k[0].push(Clause::null());
        k[1].push(Clause::null());
        ClauseMap {
            init_size_of_permanents: nc,
            next_reduction: DB_INIT_SIZE,
            kind: k,
            watches_bi: vec![NULL_CLAUSE; 2 * (nv + 1)],
            watches_per: vec![NULL_CLAUSE; 2 * (nv + 1)],
            watches_del: vec![NULL_CLAUSE; 2 * (nv + 1)],
            permutation_per: Vec::with_capacity(nv + 1),
            permutation_del: Vec::with_capacity(nv + 1),
        }
    }
}

pub fn vec2int(v: Vec<Lit>) -> Vec<i32> {
    v.iter().map(|l| l.int()).collect::<Vec<i32>>()
}

impl ClauseManagement for Solver {
    #[inline]
    fn bump_cid(&mut self, cid: ClauseId) -> () {
        debug_assert_ne!(cid, 0);
        let a;
        {
            // let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            let c = cref!(self.cp, cid);
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
    fn reduce_database(&mut self) -> () {
        let nc;
        {
            let cp = &mut self.cp[ClauseKind::Removable as usize];
            nc = cp.clauses.len();
            let perm = &mut cp.permutation;
            if perm.len() < nc {
                unsafe {
                    perm.reserve(nc + 1);
                    perm.set_len(nc + 1);
                }
            }
            // sort the range
            cp.clauses[1..].sort();
            {
                let nkeep = 1 + nc / 2;
                for mut i in 0..nc {
                    perm[cp.clauses[i].index] = i;
                }
                cp.clauses.retain(|c| perm[c.index] < nkeep || c.locked);
            }
            let new_len = cp.clauses.len();
            // update permutation table.
            for i in 1..nc {
                perm[i] = 0;
            }
            for new in 0..new_len {
                let c = &mut cp.clauses[new];
                perm[c.index] = new;
                c.index = new;
            }
            // rebuild reason
            for v in &mut self.vars[1..] {
                let cid = v.reason;
                if 0 < cid && cid.to_kind() == ClauseKind::Removable as usize {
                    v.reason = perm[cid];
                }
            }
            // rebuild watches
            for mut x in &mut cp.watcher {
                *x = NULL_CLAUSE;
            }
            for mut c in &mut cp.clauses {
                let w0 = c.lit[0].negate() as usize;
                c.next_watcher[0] = cp.watcher[w0];
                cp.watcher[w0] = c.index;
                let w1 = c.lit[1].negate() as usize;
                c.next_watcher[1] = cp.watcher[w1];
                cp.watcher[w1] = c.index;
            }
            self.next_reduction += DB_INC_SIZE + (self.c_lvl.0 as usize);
            self.stats[Stat::NumOfReduction as usize] += 1;
        }
        println!(
            "# DB::drop 1/2 Rem {:>9}, Per {:>9},Bin {:>9}   Restart:: block {:>4} force {:>4}",
            self.cp[ClauseKind::Removable as usize].clauses.len(),
            self.cp[ClauseKind::Permanent as usize].clauses.len(),
            self.cp[ClauseKind::Binclause as usize].clauses.len(),
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
        );
    }
    fn simplify_database(&mut self) -> () {
        debug_assert_eq!(self.decision_level(), 0);
        return;
        let p_end = self.cp[ClauseKind::Permanent as usize].clauses.len();
        let d_end = self.cp[ClauseKind::Removable as usize].clauses.len();
        // remove unsatisfiable literals in clauses
        let targets: Vec<Lit> = self.trail[self.num_solved_vars..]
            .iter()
            .map(|l| l.negate())
            .collect();
        for mut c in &mut self.cp[ClauseKind::Permanent as usize].clauses {
            c.lits.retain(|l| {
                for t in &targets {
                    if t == l {
                        return false;
                    }
                }
                true
            });
        }
        for mut c in &mut self.cp[ClauseKind::Removable as usize].clauses {
            c.lits.retain(|l| {
                for t in &targets {
                    if t == l {
                        return false;
                    }
                }
                true
            });
        }
        let mut p_purges = 0;
        let mut d_purges = 0;
        {
            let p_perm = &mut self.cp[ClauseKind::Permanent as usize].permutation;
            if p_perm.len() < p_end {
                unsafe {
                    p_perm.reserve(p_end);
                    p_perm.set_len(p_end);
                }
            }
            // reinitialize the permutation table.
            for x in p_perm {
                *x = 0;
            }
        }
        {
            let d_perm = &mut self.cp[ClauseKind::Removable as usize].permutation;
            if d_perm.len() < d_end {
                unsafe {
                    d_perm.reserve(d_end);
                    d_perm.set_len(d_end);
                }
            }
            for x in d_perm {
                *x = 0;
            }
        }
        // set key
        for ci in 1..self.cp[ClauseKind::Permanent as usize].clauses.len() {
            unsafe {
                let c = &mut self.cp[ClauseKind::Permanent as usize].clauses[ci] as *mut Clause;
                if self.satisfies(&*c) {
                    (*c).index = MAX;
                    p_purges += 1;
                } else if (*c).lits.len() == 0 && false {
                    if !self.enqueue((*c).lits[0], NULL_CLAUSE) {
                        self.ok = false;
                    }
                    (*c).index = MAX;
                }
            }
        }
        for ci in 1..self.cp[ClauseKind::Removable as usize].clauses.len() {
            unsafe {
                let c = &mut self.cp[ClauseKind::Removable as usize].clauses[ci] as *mut Clause;
                if self.satisfies(&*c) {
                    (*c).index = MAX;
                    d_purges += 1;
                } else if (*c).lits.len() == 0 && false {
                    if !self.enqueue((*c).lits[0], NULL_CLAUSE) {
                        self.ok = false;
                    }
                    (*c).index = MAX;
                } else {
                    let new = self.lbd_of(&(*c).lits);
                    if new < (*c).rank {
                        (*c).rank = new;
                    }
                }
            }
        }
        self.cp[ClauseKind::Permanent as usize]
            .clauses
            .retain(|ref c| c.index < MAX);
        self.cp[ClauseKind::Removable as usize]
            .clauses
            .retain(|ref c| c.index < MAX);
        let new_p_end = self.cp[ClauseKind::Permanent as usize].clauses.len();
        let new_d_end = self.cp[ClauseKind::Removable as usize].clauses.len();
        debug_assert_eq!(new_p_end, p_end - p_purges);
        debug_assert_eq!(new_d_end, d_end - d_purges);
        if new_p_end == p_end && new_d_end == d_end {
            return;
        }
        {
            let p_perm = &mut self.cp[ClauseKind::Permanent as usize].permutation;
            for i in 0..new_p_end {
                let old: usize = self.cp[ClauseKind::Permanent as usize].clauses[i].index;
                p_perm[old] = i;
                self.cp[ClauseKind::Permanent as usize].clauses[i].index = i;
            }
        }
        {
            let d_perm = &mut self.cp[ClauseKind::Removable as usize].permutation;
            for i in 0..new_d_end {
                let old = self.cp[ClauseKind::Removable as usize].clauses[i].index;
                d_perm[old] = i;
                self.cp[ClauseKind::Removable as usize].clauses[i].index = i;
            }
        }
        // clear the reasons of variables satisfied at level zero.
        for l in &self.trail {
            self.vars[l.vi() as usize].reason = NULL_CLAUSE;
        }
        self.cp[ClauseKind::Permanent as usize]
            .clauses
            .truncate(new_p_end);
        self.cp[ClauseKind::Removable as usize]
            .clauses
            .truncate(new_d_end);
        // rebuild watches for biclause and permanets
        for mut x in &mut self.cp[ClauseKind::Binclause as usize].watcher {
            *x = NULL_CLAUSE;
        }
        for mut x in &mut self.cp[ClauseKind::Permanent as usize].watcher {
            *x = NULL_CLAUSE;
        }
        for mut c in &mut self.cp[ClauseKind::Permanent as usize].clauses {
            if c.lits.len() == 0 {
                let w0 = c.lit[0].negate() as usize;
                c.next_watcher[0] = self.cp[ClauseKind::Binclause as usize].watcher[w0];
                self.cp[ClauseKind::Binclause as usize].watcher[w0] = c.index;
                let w1 = c.lit[1].negate() as usize;
                c.next_watcher[1] = self.cp[ClauseKind::Binclause as usize].watcher[w1];
                self.cp[ClauseKind::Binclause as usize].watcher[w1] = c.index;
            } else {
                let w0 = c.lit[0].negate() as usize;
                c.next_watcher[0] = self.cp[ClauseKind::Permanent as usize].watcher[w0];
                self.cp[ClauseKind::Permanent as usize].watcher[w0] = c.index;
                let w1 = c.lit[1].negate() as usize;
                c.next_watcher[1] = self.cp[ClauseKind::Permanent as usize].watcher[w1];
                self.cp[ClauseKind::Permanent as usize].watcher[w1] = c.index;
            }
        }
        // rebuild watches for deletables
        for mut x in &mut self.cp[ClauseKind::Removable as usize].watcher {
            *x = NULL_CLAUSE;
        }
        for mut c in &mut self.cp[ClauseKind::Removable as usize].clauses {
            let w0 = c.lit[0].negate() as usize;
            c.next_watcher[0] = self.cp[ClauseKind::Removable as usize].watcher[w0];
            self.cp[ClauseKind::Removable as usize].watcher[w0] = c.index;
            let w1 = c.lit[1].negate() as usize;
            c.next_watcher[1] = self.cp[ClauseKind::Removable as usize].watcher[w1];
            self.cp[ClauseKind::Removable as usize].watcher[w1] = c.index;
        }
        println!(
            "# DB::simplify {:>9} +{:>8} => {:>9} +{:>8}   Restart:: block {:>4} force {:>4}",
            d_end,
            p_end,
            new_d_end,
            new_p_end,
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
        );
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

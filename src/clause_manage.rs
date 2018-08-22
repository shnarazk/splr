use clause::ClauseIdIndexEncoding;
use clause::ClauseIndex;
use clause::ClauseKind;
use clause::ClausePack;
use clause::{CID2KIND, Clause, KERNEL_CLAUSE};
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use std::usize::MAX;
use types::*;

const DB_INIT_SIZE: usize = 1000;
const DB_INC_SIZE: usize = 50;

pub trait ClauseReference {
    /// returns ClauseId
    fn attach_clause(&mut self, c: Clause) -> ClauseId;
    fn num_learnts(&self) -> usize;
    fn iref(&self, cid: ClauseId) -> &Clause;
    fn mref(&mut self, cid: ClauseId) -> &mut Clause;
}

pub trait ClauseManagement {
    fn bump_cid(&mut self, ci: ClauseId) -> ();
    fn decay_cla_activity(&mut self) -> ();
    fn add_clause(&mut self, v: Vec<Lit>) -> bool;
    fn add_learnt(&mut self, v: Vec<Lit>) -> usize;
    fn reduce_database(&mut self) -> ();
    fn simplify_database(&mut self) -> ();
    fn lbd_of(&mut self, v: &[Lit]) -> usize;
}

pub fn cid2fmt(cid: ClauseId) -> String {
    match cid >> CID2KIND {
        0 => format!("[learnt:{}]", cid.to_index()),
        _ => format!("[prmnnt:{}]", cid.to_index()),
    }
}

struct ClauseMap2 {
    pub next_reduction: usize,
    pub kind: [ClausePack; 3],
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

impl ClauseReference for ClauseMap {
    fn iref(&self, cid: ClauseId) -> &Clause {
        &self.kind[cid.to_kind()][cid.to_index()]
    }
    fn mref(&mut self, cid: ClauseId) -> &mut Clause {
        &mut self.kind[cid.to_kind()][cid.to_index()]
    }
    fn attach_clause(&mut self, mut c: Clause) -> ClauseId {
        let cid: ClauseId;
        let w0 = c.lit[0].negate() as usize;
        let w1 = c.lit[1].negate() as usize;
        if c.learnt && 0 < c.lits.len() {
            cid = self.kind[ClauseKind::Deletable as usize].len();
            c.index = cid;
            let top = self.watches_del[w0];
            c.next_watcher[0] = top;
            self.watches_del[w0] = cid;
            let top = self.watches_del[w1];
            c.next_watcher[1] = top;
            self.watches_del[w1] = cid;
            println!("new learnt {} {}", cid, c);
            self.kind[ClauseKind::Deletable as usize].push(c);
            cid
        } else {
            cid = self.kind[ClauseKind::Permanent as usize].len();
            let len = c.lits.len();
            c.index = cid;
            if len == 0 {
                let top = self.watches_bi[w0];
                c.next_watcher[0] = top;
                self.watches_bi[w0] = cid;
                let top = self.watches_bi[w1];
                c.next_watcher[1] = top;
                self.watches_bi[w1] = cid;
            } else {
                let top = self.watches_per[w0];
                c.next_watcher[0] = top;
                self.watches_per[w0] = cid;
                let top = self.watches_per[w1];
                c.next_watcher[1] = top;
                self.watches_per[w1] = cid;
            }
            self.kind[ClauseKind::Permanent as usize].push(c);
            cid | KERNEL_CLAUSE
        }
    }
    fn num_learnts(&self) -> usize {
        self.kind[ClauseKind::Deletable as usize].len()
    }
}

impl ClauseManagement for Solver {
    #[inline]
    fn bump_cid(&mut self, cid: ClauseId) -> () {
        debug_assert_ne!(cid, 0);
        let a;
        {
            let c = self.clauses.mref(cid);
            a = c.activity + self.cla_inc;
            c.activity = a;
        }
        if 1.0e20 < a {
            for c in &mut self.clauses.kind[ClauseKind::Deletable as usize] {
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
        match v.len() {
            0 => true,
            1 => self.enqueue(v[0], NULL_CLAUSE),
            _ => {
                self.clauses.attach_clause(Clause::new(false, 0, v));
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
        let cid = self.clauses.attach_clause(Clause::new(true, lbd, v));
        self.bump_cid(cid);
        self.uncheck_enqueue(l0, cid);
        lbd
    }
    fn reduce_database(&mut self) -> () {
        return;
        let nc = self.clauses.kind[ClauseKind::Deletable as usize].len();
        let perm = &mut self.clauses.permutation_del;
        if perm.len() < nc {
            unsafe {
                perm.reserve(nc + 1);
                perm.set_len(nc + 1);
            }
        }
        // sort the range
        self.clauses.kind[ClauseKind::Deletable as usize].sort();
        {
            let nkeep = 1 + nc / 2;
            for mut i in 0..nc {
                perm[self.clauses.kind[ClauseKind::Deletable as usize][i].index] = i;
            }
            self.clauses.kind[ClauseKind::Deletable as usize]
                .retain(|c| perm[c.index] < nkeep || c.locked);
        }
        let new_len = self.clauses.kind[ClauseKind::Deletable as usize].len();
        // update permutation table.
        for i in 0..nc {
            perm[i] = 0;
        }
        for new in 0..new_len {
            let c = &mut self.clauses.kind[ClauseKind::Deletable as usize][new];
            perm[c.index] = new;
            c.index = new;
        }
        // rebuild reason
        for v in &mut self.vars[1..] {
            let cid = v.reason;
            if v.reason & KERNEL_CLAUSE == 0 {
                v.reason = perm[cid];
            }
        }
        // rebuild watches for permanents
        for mut x in &mut self.clauses.watches_per {
            *x = NULL_CLAUSE;
        }
        for mut c in &mut self.clauses.kind[ClauseKind::Deletable as usize] {
            let w0 = c.lit[0].negate() as usize;
            c.next_watcher[0] = self.clauses.watches_per[w0];
            self.clauses.watches_del[w0 as usize] = c.index;
            let w1 = c.lit[1].negate() as usize;
            c.next_watcher[1] = self.clauses.watches_per[w1];
            self.clauses.watches_del[w1] = c.index;
        }
        // rebuild watches for deletables
        for mut x in &mut self.clauses.watches_del {
            *x = NULL_CLAUSE;
        }
        for mut c in &mut self.clauses.kind[ClauseKind::Deletable as usize] {
            let w0 = c.lit[0].negate() as usize;
            c.next_watcher[0] = self.clauses.watches_del[w0];
            self.clauses.watches_del[w0 as usize] = c.index;
            let w1 = c.lit[1].negate() as usize;
            c.next_watcher[1] = self.clauses.watches_del[w1];
            self.clauses.watches_del[w1] = c.index;
        }
        self.clauses.next_reduction += DB_INC_SIZE + (self.c_lvl.0 as usize);
        self.stats[Stat::NumOfReduction as usize] += 1;
        println!(
            "# DB::drop 1/2 {:>9} +{:>8} => {:>9} +{:>8}   Restart:: block {:>4} force {:>4}",
            nc,
            self.clauses.kind[ClauseKind::Permanent as usize].len(),
            new_len,
            self.clauses.kind[ClauseKind::Permanent as usize].len(),
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
        );
    }
    fn simplify_database(&mut self) -> () {
        return;
        debug_assert_eq!(self.decision_level(), 0);
        let p_end = self.clauses.kind[ClauseKind::Permanent as usize].len();
        let d_end = self.clauses.kind[ClauseKind::Deletable as usize].len();
        // remove unsatisfiable literals in clauses
        let targets: Vec<Lit> = self.trail[self.num_solved_vars..]
            .iter()
            .map(|l| l.negate())
            .collect();
        for mut c in &mut self.clauses.kind[ClauseKind::Permanent as usize] {
            c.lits.retain(|l| {
                for t in &targets {
                    if t == l {
                        return false;
                    }
                }
                true
            });
        }
        for mut c in &mut self.clauses.kind[ClauseKind::Deletable as usize] {
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
            let p_perm = &mut self.clauses.permutation_per;
            if p_perm.len() < p_end {
                unsafe {
                    p_perm.reserve(p_end);
                    p_perm.set_len(p_end);
                }
            }
            let d_perm = &mut self.clauses.permutation_del;
            if d_perm.len() < d_end {
                unsafe {
                    d_perm.reserve(d_end);
                    d_perm.set_len(d_end);
                }
            }
            // reinitialize the permutation table.
            for x in p_perm {
                *x = 0;
            }
            for x in d_perm {
                *x = 0;
            }
        }
        // set key
        for ci in 1..self.clauses.kind[ClauseKind::Permanent as usize].len() {
            unsafe {
                let c = &mut self.clauses.kind[ClauseKind::Permanent as usize][ci] as *mut Clause;
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
        for ci in 1..self.clauses.kind[ClauseKind::Deletable as usize].len() {
            unsafe {
                let c = &mut self.clauses.kind[ClauseKind::Deletable as usize][ci] as *mut Clause;
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
        self.clauses.kind[ClauseKind::Permanent as usize].retain(|ref c| c.index < MAX);
        self.clauses.kind[ClauseKind::Deletable as usize].retain(|ref c| c.index < MAX);
        let new_p_end = self.clauses.kind[ClauseKind::Permanent as usize].len();
        let new_d_end = self.clauses.kind[ClauseKind::Deletable as usize].len();
        debug_assert_eq!(new_p_end, p_end - p_purges);
        debug_assert_eq!(new_d_end, d_end - d_purges);
        if new_p_end == p_end && new_d_end == d_end {
            return;
        }
        {
            let p_perm = &mut self.clauses.permutation_per;
            for i in 0..new_p_end {
                let old: usize = self.clauses.kind[ClauseKind::Permanent as usize][i].index;
                p_perm[old] = i;
                self.clauses.kind[ClauseKind::Permanent as usize][i].index = i;
            }
        }
        {
            let d_perm = &mut self.clauses.permutation_del;
            for i in 0..new_d_end {
                let old = self.clauses.kind[ClauseKind::Deletable as usize][i].index;
                d_perm[old] = i;
                self.clauses.kind[ClauseKind::Deletable as usize][i].index = i;
            }
        }
        // clear the reasons of variables satisfied at level zero.
        for l in &self.trail {
            self.vars[l.vi() as usize].reason = NULL_CLAUSE;
        }
        self.clauses.kind[ClauseKind::Permanent as usize].truncate(new_p_end);
        self.clauses.kind[ClauseKind::Deletable as usize].truncate(new_d_end);
        // rebuild watches for biclause and permanets
        for mut x in &mut self.clauses.watches_bi {
            *x = NULL_CLAUSE;
        }
        for mut x in &mut self.clauses.watches_per {
            *x = NULL_CLAUSE;
        }
        for mut c in &mut self.clauses.kind[ClauseKind::Permanent as usize] {
            if c.lits.len() == 0 {
                let w0 = c.lit[0].negate() as usize;
                c.next_watcher[0] = self.clauses.watches_bi[w0];
                self.clauses.watches_bi[w0] = c.index;
                let w1 = c.lit[1].negate() as usize;
                c.next_watcher[1] = self.clauses.watches_bi[w1];
                self.clauses.watches_bi[w1] = c.index;
            } else {
                let w0 = c.lit[0].negate() as usize;
                c.next_watcher[0] = self.clauses.watches_per[w0];
                self.clauses.watches_per[w0] = c.index;
                let w1 = c.lit[1].negate() as usize;
                c.next_watcher[1] = self.clauses.watches_per[w1];
                self.clauses.watches_per[w1] = c.index;
            }
        }
        // rebuild watches for deletables
        for mut x in &mut self.clauses.watches_del {
            *x = NULL_CLAUSE;
        }
        for mut c in &mut self.clauses.kind[ClauseKind::Deletable as usize] {
            let w0 = c.lit[0].negate() as usize;
            c.next_watcher[0] = self.clauses.watches_del[w0];
            self.clauses.watches_del[w0 as usize] = c.index;
            let w1 = c.lit[1].negate() as usize;
            c.next_watcher[1] = self.clauses.watches_del[w1];
            self.clauses.watches_del[w1] = c.index;
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

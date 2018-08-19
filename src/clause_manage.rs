use clause::{Clause, RANK_CONST, RANK_NEED};
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use std::usize::MAX;
use types::*;

const KERNEL_CLAUSE: usize = 0xc00_0000_0000_0000;

pub trait ClauseReference {
    fn iref(&self, cid: ClauseIndex) -> &Clause;
    fn mref(&mut self, cid: ClauseIndex) -> &mut Clause;
    fn push(&mut self, learnt: bool, c: Clause) -> ClauseIndex;
    fn num_learnts(&self) -> usize;
}

pub trait ClauseManagement {
    fn bump_ci(&mut self, ci: ClauseIndex) -> ();
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
    pub nb_clauses_before_reduce: usize,
    pub permanents: Vec<Clause>,
    pub deletables: Vec<Clause>,
    pub permutation: Vec<ClauseIndex>,
}

impl ClauseMap {
    pub fn new(n: usize) -> ClauseMap {
        let mut p = Vec::with_capacity(n+1);
        p.push(Clause::null());
        ClauseMap {
            init_size_of_permanents: n,
            nb_clauses_before_reduce: 2000,
            permanents: Vec::with_capacity(n),
            deletables: p,
            permutation: Vec::with_capacity(n),
        }
    }
}

pub fn vec2int(v: Vec<Lit>) -> Vec<i32> {
    v.iter().map(|l| l.int()).collect::<Vec<i32>>()
}

impl ClauseReference for ClauseMap {
    #[inline]
    fn iref(&self, cid: ClauseIndex) -> &Clause {
        if KERNEL_CLAUSE <= cid
        {
            &self.permanents[cid - KERNEL_CLAUSE]
        } else {
            &self.deletables[cid]
        }
    }
    #[inline]
    fn mref(&mut self, cid: ClauseIndex) -> &mut Clause {
        if KERNEL_CLAUSE <= cid
        {
            &mut self.permanents[cid - KERNEL_CLAUSE]
        } else {
            &mut self.deletables[cid]
        }
    }
    fn push(&mut self, learnt: bool, mut c: Clause) -> ClauseIndex {
        let cid: ClauseIndex;
        if learnt && 2 < c.lits.len() {
            cid = self.deletables.len();
            c.index = cid;
            self.deletables.push(c);
        } else {
            cid = KERNEL_CLAUSE + self.permanents.len();
            c.index = cid;
            self.permanents.push(c);
        }
        cid
    }
    fn num_learnts(&self) -> usize {
        self.deletables.len()
    }

}

impl ClauseManagement for Solver {
    fn bump_ci(&mut self, ci: ClauseIndex) -> () {
        debug_assert_ne!(ci, 0);
        let a = self.clauses.iref(ci).activity + self.cla_inc;
        self.clauses.mref(ci).activity = a;
        if 1.0e20 < a {
            for c in &mut self.clauses.deletables {
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
                self.attach_clause(false, Clause::new(RANK_CONST, v));
                true
            }
        }
    }
    /// renamed from newLearntClause
    fn add_learnt(&mut self, v: Vec<Lit>) -> usize {
        let lbd;
        if v.len() == 2 {
            lbd = 0;
        } else {
            lbd = self.lbd_of(&v);
        }
        let mut c = Clause::new(RANK_NEED + lbd, v);
        let mut i_max = 0;
        let mut lv_max = 0;
        // seek a literal with max level
        for i in 0..c.lits.len() {
            let vi = c.lits[i].vi();
            let lv = self.vars[vi].level;
            if self.vars[vi].assign != BOTTOM && lv_max < lv {
                i_max = i;
                lv_max = lv;
            }
        }
        c.lits.swap(1, i_max);
        let l0 = c.lits[0];
        let ci = self.attach_clause(true, c);
        self.bump_ci(ci);
        self.uncheck_enqueue(l0, ci);
        lbd
    }
    fn reduce_database(&mut self) -> () {
        let start = 1;
        let nc = self.clauses.deletables.len();
        let perm = &mut self.clauses.permutation;
        if perm.len() < nc {
            unsafe {
                perm.reserve(nc + 1);
                perm.set_len(nc + 1);
            }
        }
        // sort the range
        self.clauses.deletables.sort();
        {
            for mut i in 0..nc {
                perm[self.clauses.deletables[i].index] = i;
            }
            let _ac = 0.1 * self.cla_inc / ((nc - start) as f64);
            let nkeep = start + (nc - start) / 2;
            // println!("ac {}, pased {}, index {}, locked {}, activity threshold {}",
            //          ac,
            //          self.clauses[start..].iter().filter(|c| c.locked || ac < c.activity).count(),
            //          self.clauses[start..].iter().filter(|c| perm[c.index] < nkeep).count(),
            //          self.clauses[start..].iter().filter(|c| c.locked).count(),
            //          self.clauses[start..].iter().filter(|c| ac < c.activity).count(),
            //          );
            self.clauses.deletables.retain(|c| perm[c.index] < nkeep || c.locked);
            // println!("start {}, end {}, nkeep {}, new len {}", start, nc, nkeep, self.clauses.len());
        }
        let new_len = self.clauses.deletables.len();
        // update permutation table.
        for i in 0..nc {
            perm[i] = 0;
        }
        for new in 0..new_len {
            let c = &mut self.clauses.deletables[new];
            perm[c.index] = new;
            c.index = new;
        }
        // rebuild reason
        for v in &mut self.vars[1..] {
            let cid = v.reason;
            if cid < KERNEL_CLAUSE {
                v.reason = perm[cid];
            }
        }
        // rebuild bi_watches
        for v in &mut self.bi_watches {
            for w in &mut v[..] {
                let cid = w.by;
                if cid < KERNEL_CLAUSE {
                    w.by = perm[cid];
                }
            }
        }
        // rebuild watches
        for v in &mut self.watches {
            for w in &mut v[..] {
                let cid = w.by;
                if cid < KERNEL_CLAUSE {
                    w.by = perm[w.by];
                }
            }
        }
        self.clauses.nb_clauses_before_reduce += 300;
        self.stats[Stat::NumOfReduction as usize] += 1;
        println!(
            "# DB::drop 1/2 {:>9}({:>8}) => {:>9}   Restart:: block {:>4} force {:>4}",
            nc,
            self.clauses.permanents.len(),
            new_len,
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
        );
    }
    fn simplify_database(&mut self) -> () {
        debug_assert_eq!(self.decision_level(), 0);
        // permanents
        let end = self.clauses.permanents.len();
        // remove clauses containing new fixed literals
        let targets: Vec<Lit> = self.trail[self.num_solved_vars..]
            .iter()
            .map(|l| l.negate())
            .collect();
        for mut c in &mut self.clauses.permanents {
            c.lits.retain(|l| {
                for t in &targets {
                    if t == l {
                        return false;
                    }
                }
                true
            });
        }
        let nc = self.clauses.permanents.len();
        let mut purges = 0;
{
        let perm = &mut self.clauses.permutation;
        if perm.len() < nc {
            unsafe {
                perm.reserve(nc + 1);
                perm.set_len(nc + 1);
            }
        }
        // reinitialize the permutation table.
        for x in perm {
            *x = 0;
        }
}
        // set key
        for ci in 1..self.clauses.permanents.len() {
            unsafe {
                let c = &mut self.clauses.permanents[ci] as *mut Clause;
                if self.satisfies(&self.clauses.permanents[ci]) {
                    (*c).index = MAX;
                    purges += 1;
                } else if (*c).lits.len() == 1 {
                    if !self.enqueue((*c).lits[0], NULL_CLAUSE) {
                        self.ok = false;
                    }
                    (*c).index = MAX;
                } else {
                    if RANK_NEED < (*c).rank {
                        let new = self.lbd_of(&(*c).lits);
                        if new < (*c).rank {
                            (*c).rank = new;
                        }
                    }
                }
            }
        }
        self.clauses.permanents.retain(|ref c| c.index < MAX);
        let new_end = self.clauses.permanents.len();
        debug_assert_eq!(new_end, nc - purges);
{
        let perm = &mut self.clauses.permutation;
        for i in 1..new_end {
            let old = self.clauses.permanents[i].index;
            debug_assert!(0 < old, "0 index");
            perm[old] = i;
            self.clauses.permanents[i].index = i;
        }
}
        // clear the reasons of variables satisfied at level zero.
        for l in &self.trail {
            self.vars[l.vi() as usize].reason = NULL_CLAUSE;
        }
        let mut c0 = 0;
        for c in &self.clauses.permanents[..] {
            if c.rank <= RANK_NEED {
                c0 += 1;
            } else {
                break;
            }
        }
        if new_end == end {
            return;
        }
        self.clauses.permanents.truncate(new_end);
        {
            // rebuild bi_watches
            let perm = &mut self.clauses.permutation;
           let (w0, wr) = self.bi_watches.split_first_mut().unwrap();
            w0.clear();
            for ws in wr {
                while let Some(mut w) = ws.pop() {
                    match perm[w.by] {
                        0 => {}
                        x => {
                            w.by = x;
                            w0.push(w);
                        }
                    }
                }
                while let Some(w) = w0.pop() {
                    ws.push(w);
                }
            }
        }
        {
            // rebuild watches
            let (w0, wr) = self.watches.split_first_mut().unwrap();
            let perm = &mut self.clauses.permutation;
            w0.clear();
            for ws in wr {
                while let Some(mut w) = ws.pop() {
                    match perm[w.by] {
                        0 => {}
                        x => {
                            w.by = x;
                            w0.push(w);
                        }
                    }
                }
                while let Some(w) = w0.pop() {
                    ws.push(w);
                }
            }
        }
        println!(
            "# DB::simplify {:>9}({:>8}) => {:>9}   Restart:: block {:>4} force {:>4}",
            nc,
            self.clauses.permanents.len(),
            self.clauses.deletables.len(),
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
        );
    }
    fn lbd_of(&mut self, v: &[Lit]) -> usize {
        if v.len() == 2 {
            return RANK_NEED;
        }
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

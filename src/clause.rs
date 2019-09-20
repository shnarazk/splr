use crate::config::{Config, ACTIVITY_MAX};
use crate::eliminator::Eliminator;
use crate::propagator::AssignStack;
use crate::state::{Stat, State};
use crate::traits::*;
use crate::types::*;
use crate::var::VarDB;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Index, IndexMut, Range, RangeFrom};

#[derive(Debug, Eq, PartialEq)]
pub enum CertifiedRecord {
    SENTINEL,
    ADD,
    DELETE,
}

type DRAT = Vec<(CertifiedRecord, Vec<i32>)>;

impl ClauseIdIF for ClauseId {
    fn to_lit(self) -> Lit {
        (self & 0x7FFF_FFFF) as Lit
    }
    fn is_lifted_lit(self) -> bool {
        0 != 0x8000_0000 & self
    }
    fn format(self) -> String {
        if self == NULL_CLAUSE {
            "NullClause".to_string()
        } else {
            format!("C::{}", self)
        }
    }
}

/// 'watch literal' structure
#[derive(Clone, Debug)]
pub struct Watch {
    /// a cache of a literal in the clause
    pub blocker: Lit,
    /// ClauseId
    pub c: ClauseId,
}

impl Default for Watch {
    fn default() -> Watch {
        Watch {
            blocker: NULL_LIT,
            c: NULL_CLAUSE,
        }
    }
}

impl WatchDBIF for Vec<Watch> {
    fn initialize(self, _n: usize) -> Self {
        self
    }
    fn register(&mut self, blocker: Lit, c: ClauseId) {
        self.push(Watch { blocker, c });
    }
    fn detach(&mut self, n: usize) {
        self.swap_remove(n);
    }
    fn detach_with(&mut self, cid: ClauseId) {
        for (n, w) in self.iter().enumerate() {
            if w.c == cid {
                self.swap_remove(n);
                return;
            }
        }
    }
    fn update_blocker(&mut self, cid: ClauseId, l: Lit) {
        for w in &mut self[..] {
            if w.c == cid {
                w.blocker = l;
                return;
            }
        }
    }
}

/// A representation of 'clause'
#[derive(Debug)]
pub struct Clause {
    /// The literals in a clause.
    pub lits: Vec<Lit>,
    /// A static clause evaluation criterion like LBD, NDD, or something.
    pub rank: usize,
    /// A dynamic clause evaluation criterion based on the number of references.
    pub activity: f64,
    /// Flags
    flags: Flag,
}

impl Default for Clause {
    fn default() -> Clause {
        Clause {
            lits: vec![],
            rank: 0,
            activity: 0.0,
            flags: Flag::empty(),
        }
    }
}

impl ClauseIF for Clause {
    fn kill(&mut self, touched: &mut [bool]) {
        self.turn_on(Flag::DEAD);
        debug_assert!(1 < self.lits[0] && 1 < self.lits[1]);
        touched[self.lits[0].negate() as usize] = true;
        touched[self.lits[1].negate() as usize] = true;
    }
}

impl FlagIF for Clause {
    fn is(&self, flag: Flag) -> bool {
        self.flags.contains(flag)
    }
    fn turn_off(&mut self, flag: Flag) {
        self.flags.remove(flag);
    }
    fn turn_on(&mut self, flag: Flag) {
        self.flags.insert(flag);
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Clause) -> bool {
        self == other
    }
}

impl Eq for Clause {}

impl PartialOrd for Clause {
    fn partial_cmp(&self, other: &Clause) -> Option<Ordering> {
        if self.rank < other.rank {
            Some(Ordering::Less)
        } else if other.rank < self.rank {
            Some(Ordering::Greater)
        } else if self.activity > other.activity {
            Some(Ordering::Less)
        } else if other.activity > self.activity {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl Ord for Clause {
    fn cmp(&self, other: &Clause) -> Ordering {
        if self.rank < other.rank {
            Ordering::Less
        } else if other.rank > self.rank {
            Ordering::Greater
        } else if self.activity > other.activity {
            Ordering::Less
        } else if other.activity > self.activity {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

impl Clause {
    #[allow(dead_code)]
    fn cmp_activity(&self, other: &Clause) -> Ordering {
        if self.activity > other.activity {
            Ordering::Less
        } else if other.activity > self.activity {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(
            f,
            "C{{{:?} {}{}}}",
            vec2int(&self.lits),
            st(Flag::DEAD, ", dead"),
            st(Flag::ENQUEUED, ", enqueued"),
        )
    }
}

/// Clause database
#[derive(Debug)]
pub struct ClauseDB {
    clause: Vec<Clause>,
    pub touched: Vec<bool>,
    pub watcher: Vec<Vec<Watch>>,
    pub num_active: usize,
    pub num_learnt: usize,
    pub certified: DRAT,
    pub activity_inc: f64,
    pub activity_decay: f64,
    pub inc_step: usize,
    extra_inc: usize,
    pub soft_limit: usize,
    pub co_lbd_bound: usize,
    pub lbd_frozen_clause: usize,
    pub first_reduction: usize,
    pub next_reduction: usize, // renamed from `nbclausesbeforereduce`
    pub glureduce: bool,
}

impl Index<ClauseId> for ClauseDB {
    type Output = Clause;
    fn index(&self, cid: ClauseId) -> &Clause {
        unsafe { self.clause.get_unchecked(cid as usize) }
    }
}

impl IndexMut<ClauseId> for ClauseDB {
    fn index_mut(&mut self, cid: ClauseId) -> &mut Clause {
        unsafe { self.clause.get_unchecked_mut(cid as usize) }
    }
}

impl Index<Range<usize>> for ClauseDB {
    type Output = [Clause];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Clause] {
        &self.clause[r]
    }
}

impl Index<RangeFrom<usize>> for ClauseDB {
    type Output = [Clause];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Clause] {
        &self.clause[r]
    }
}

impl IndexMut<Range<usize>> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Clause] {
        &mut self.clause[r]
    }
}

impl IndexMut<RangeFrom<usize>> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Clause] {
        &mut self.clause[r]
    }
}

impl ActivityIF for ClauseDB {
    type Ix = ClauseId;
    fn bump_activity(&mut self, cid: Self::Ix) {
        let c = &mut self.clause[cid as usize];
        let a = c.activity + self.activity_inc;
        c.activity = a;
        if ACTIVITY_MAX < a {
            let scale = 1.0 / self.activity_inc;
            for c in &mut self.clause[1..] {
                if c.is(Flag::LEARNT) {
                    c.activity *= scale;
                }
            }
            self.activity_inc *= scale;
        }
    }
    fn scale_activity(&mut self) {
        self.activity_inc /= self.activity_decay;
    }
}

impl Instantiate for ClauseDB {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> ClauseDB {
        let nv = cnf.num_of_variables;
        let nc = cnf.num_of_clauses;
        let mut clause = Vec::with_capacity(1 + nc);
        clause.push(Clause::default());
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        let mut touched = Vec::with_capacity(2 * (nv + 1));
        for _ in 0..2 * (nv + 1) {
            watcher.push(Vec::new());
            touched.push(false);
        }
        let mut certified = Vec::new();
        if config.use_certification {
            certified.push((CertifiedRecord::SENTINEL, Vec::new()));
        }
        ClauseDB {
            clause,
            touched,
            watcher,
            num_active: 0,
            num_learnt: 0,
            certified,
            activity_inc: 1.0,
            activity_decay: 0.999,
            inc_step: 300,
            extra_inc: 1000,
            soft_limit: config.clause_limit, // 248_000_000
            co_lbd_bound: 5,
            lbd_frozen_clause: 30,
            first_reduction: 1000,
            next_reduction: 1000,
            glureduce: true,
        }
    }
}

impl ClauseDBIF for ClauseDB {
    fn len(&self) -> usize {
        self.clause.len()
    }
    fn is_empty(&self) -> bool {
        self.clause.is_empty()
    }
    fn garbage_collect(&mut self) {
        // debug_assert!(self.check_liveness1());
        let ClauseDB {
            ref mut watcher,
            ref mut clause,
            ref mut touched,
            ref mut certified,
            ..
        } = self;
        debug_assert_eq!(NULL_LIT.negate(), 1);
        let (recycles, wss) = watcher.split_at_mut(2);
        let recycled = &mut recycles[1];
        for (i, ws) in &mut wss.iter_mut().enumerate() {
            if !touched[i + 2] {
                continue;
            }
            touched[i + 2] = false;
            let mut n = 0;
            while n < ws.len() {
                let cid = ws[n].c;
                let c = &mut clause[cid as usize];
                if !c.is(Flag::DEAD) {
                    n += 1;
                    continue;
                }
                if !c.lits.is_empty() {
                    debug_assert!(c.is(Flag::DEAD));
                    recycled.push(Watch {
                        blocker: NULL_LIT,
                        c: cid,
                    });
                    if c.is(Flag::LEARNT) {
                        self.num_learnt -= 1;
                    }
                    if !certified.is_empty() {
                        let temp = c.lits.iter().map(|l| l.to_i32()).collect::<Vec<i32>>();
                        certified.push((CertifiedRecord::ADD, temp));
                    }
                    c.lits.clear();
                }
                ws.detach(n);
            }
        }
        self.num_active = self.clause.len() - recycled.len();
        // debug_assert!(self.check_liveness2());
    }
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool) -> ClauseId {
        let cid;
        let l0 = v[0];
        let l1 = v[1];
        if let Some(w) = self.watcher[NULL_LIT.negate() as usize].pop() {
            cid = w.c;
            let c = &mut self.clause[cid as usize];
            // if !c.is(Flag::DEAD) {
            //     println!("{} {:?}", cid.format(), vec2int(&c.lits));
            //     println!("len {}", self.watcher[NULL_LIT.negate() as usize].len());
            //     for w in &self.watcher[NULL_LIT.negate() as usize][..10] {
            //         if !self.clause[w.c].is(Flag::DEAD) {
            //             println!("{}", w.c.format());
            //         }
            //     }
            //     panic!("done");
            // }
            debug_assert!(c.is(Flag::DEAD));
            c.flags = Flag::empty();
            c.lits.clear();
            for l in v {
                c.lits.push(*l);
            }
            c.rank = rank;
            c.activity = 0.0;
        } else {
            let mut lits = Vec::with_capacity(v.len());
            for l in v {
                lits.push(*l);
            }
            cid = self.clause.len() as ClauseId;
            let c = Clause {
                flags: Flag::empty(),
                lits,
                rank,
                activity: 0.0,
            };
            self.clause.push(c);
        };
        let c = &mut self.clause[cid as usize];
        if learnt {
            c.turn_on(Flag::LEARNT);
            self.num_learnt += 1;
        }
        self.watcher[l0.negate() as usize].register(l1, cid);
        self.watcher[l1.negate() as usize].register(l0, cid);
        self.num_active += 1;
        cid
    }
    fn reset_lbd(&mut self, vars: &VarDB, temp: &mut [usize]) {
        let mut key = temp[0];
        for c in &mut self.clause[1..] {
            if c.is(Flag::DEAD) || c.is(Flag::LEARNT) {
                continue;
            }
            key += 1;
            let mut cnt = 0;
            for l in &c.lits {
                let lv = vars[l.vi()].level;
                if temp[lv] != key && lv != 0 {
                    temp[lv] = key;
                    cnt += 1;
                }
            }
            c.rank = cnt;
        }
        temp[0] = key + 1;
    }
    fn count(&self, alive: bool) -> usize {
        if alive {
            self.clause.len() - self.watcher[NULL_LIT.negate() as usize].len() - 1
        } else {
            self.clause.len() - 1
        }
    }
    fn countf(&self, mask: Flag) -> usize {
        self.clause
            .iter()
            .skip(1)
            .filter(|&c| c.flags.contains(mask) && !c.flags.contains(Flag::DEAD))
            .count()
    }
    // Note: set lbd to 0 if you want to add the clause to Permanent.
    fn attach(&mut self, state: &mut State, vars: &mut VarDB, lbd: usize) -> ClauseId {
        let v = &mut state.new_learnt;
        if !self.certified.is_empty() {
            let temp = v.iter().map(|l| l.to_i32()).collect::<Vec<i32>>();
            self.certified.push((CertifiedRecord::ADD, temp));
        }
        debug_assert!(1 < v.len());
        let mut i_max = 0;
        let mut lv_max = 0;
        // seek a literal with max level
        for (i, l) in v.iter().enumerate() {
            let vi = l.vi();
            let lv = vars[vi].level;
            if vars[vi].assign != BOTTOM && lv_max < lv {
                i_max = i;
                lv_max = lv;
            }
        }
        v.swap(1, i_max);
        let learnt = 0 < lbd && 2 < v.len() && (!state.use_chan_seok || self.co_lbd_bound < lbd);
        let cid = self.new_clause(&v, lbd, learnt);
        let c = &mut self.clause[cid as usize];
        c.activity = self.activity_inc;
        cid
    }
    fn detach(&mut self, cid: ClauseId) {
        let c = &mut self.clause[cid as usize];
        debug_assert!(!c.is(Flag::DEAD));
        debug_assert!(1 < c.lits.len());
        c.kill(&mut self.touched);
    }
    fn reduce(&mut self, state: &mut State, vars: &mut VarDB) {
        self.reset_lbd(vars, &mut state.lbd_temp);
        let ClauseDB {
            ref mut clause,
            ref mut touched,
            ..
        } = self;
        self.next_reduction += self.inc_step;
        let mut perm = Vec::with_capacity(clause.len());
        for (i, b) in clause.iter().enumerate().skip(1) {
            if b.is(Flag::LEARNT) && !b.is(Flag::DEAD) && !vars.locked(b, i as ClauseId) {
                perm.push(i);
            }
        }
        if perm.is_empty() {
            return;
        }
        let keep = perm.len() / 2;
        if state.use_chan_seok {
            perm.sort_by(|&a, &b| clause[a].cmp_activity(&clause[b]));
        } else {
            perm.sort_by(|&a, &b| clause[a].cmp(&clause[b]));
            if clause[perm[keep]].rank <= 3 {
                self.next_reduction += self.extra_inc;
            }
            if clause[perm[0]].rank <= 5 {
                self.next_reduction += self.extra_inc;
            };
        }
        for i in &perm[keep..] {
            let c = &mut clause[*i];
            if c.is(Flag::JUST_USED) {
                c.turn_off(Flag::JUST_USED)
            }
            if 2 < c.rank {
                c.kill(touched);
            }
        }
        state.stats[Stat::Reduction] += 1;
        self.garbage_collect();
    }
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        elim: &mut Eliminator,
        state: &mut State,
        vars: &mut VarDB,
    ) -> MaybeInconsistent {
        debug_assert_eq!(asgs.level(), 0);
        // we can reset all the reasons because decision level is zero.
        for v in &mut vars[1..] {
            v.reason = NULL_CLAUSE;
        }
        if elim.is_waiting() {
            self.reset();
            elim.prepare(self, vars, true);
        }
        loop {
            let na = asgs.len();
            elim.eliminate(asgs, self, state, vars)?;
            self.eliminate_satisfied_clauses(elim, vars, true);
            if na == asgs.len()
                && (!elim.is_running()
                    || (0 == elim.clause_queue_len() && 0 == elim.var_queue_len()))
            {
                break;
            }
        }
        self.garbage_collect();
        state.stats[Stat::SatClauseElimination] += 1;
        if elim.is_running() {
            state.stats[Stat::ExhaustiveElimination] += 1;
            self.reset_lbd(vars, &mut state.lbd_temp);
            elim.stop(self, vars);
        }
        if self.check_size().is_err() {
            Err(SolverError::Inconsistent)
        } else {
            Ok(())
        }
    }
    fn reset(&mut self) {
        debug_assert!(1 < self.clause.len());
        for c in &mut self.clause[1..] {
            if c.is(Flag::LEARNT) && !c.is(Flag::DEAD) && self.co_lbd_bound < c.lits.len() {
                c.kill(&mut self.touched);
            }
        }
        self.garbage_collect();
    }
    fn certificate_add(&mut self, vec: &[Lit]) {
        if !self.certified.is_empty() {
            let temp = vec.iter().map(|l| l.to_i32()).collect::<Vec<i32>>();
            self.certified.push((CertifiedRecord::ADD, temp));
        }
    }
    fn certificate_delete(&mut self, vec: &[Lit]) {
        if !self.certified.is_empty() {
            let temp = vec.iter().map(|l| l.to_i32()).collect::<Vec<i32>>();
            self.certified.push((CertifiedRecord::DELETE, temp));
        }
    }
    fn eliminate_satisfied_clauses(
        &mut self,
        elim: &mut Eliminator,
        vars: &mut VarDB,
        update_occur: bool,
    ) {
        for (cid, c) in &mut self.clause.iter_mut().enumerate().skip(1) {
            if !c.is(Flag::DEAD) && vars.satisfies(&c.lits) {
                c.kill(&mut self.touched);
                if elim.is_running() {
                    if update_occur {
                        elim.remove_cid_occur(vars, cid as ClauseId, c);
                    }
                    for l in &c.lits {
                        let v = &mut vars[l.vi()];
                        if !v.is(Flag::ELIMINATED) {
                            elim.enqueue_var(vars, l.vi(), true);
                        }
                    }
                }
            }
        }
    }
    fn check_size(&self) -> MaybeInconsistent {
        if self.soft_limit == 0 || self.count(false) <= self.soft_limit {
            Ok(())
        } else {
            Err(SolverError::Inconsistent)
        }
    }
    fn make_permanent(&mut self, reinit: bool) {
        // Adjusting for low decision levels.
        // move some clauses with good lbd (col_lbd_bound) to Permanent
        for c in &mut self.clause[1..] {
            if c.is(Flag::DEAD) || !c.is(Flag::LEARNT) {
                continue;
            }
            if c.rank <= self.co_lbd_bound {
                c.turn_off(Flag::LEARNT);
                self.num_learnt -= 1;
            } else if reinit {
                c.kill(&mut self.touched);
            }
        }
        self.garbage_collect();
    }
}

/*
impl ClauseDB {
    #[allow(dead_code)]
    fn check_liveness1(&self) -> bool {
        let deads = self.watcher[NULL_LIT.negate() as usize]
            .iter()
            .map(|w| w.c)
            .collect::<Vec<ClauseId>>();
        for cid in deads {
            if !self.clause[cid as usize].is(Flag::DEAD) {
                panic!("done");
            }
        }
        for cid in 1..self.clause.len() {
            if !self.clause[cid].is(Flag::DEAD) {
                let lits = &self.clause[cid].lits;
                if lits.len() < 2 {
                    panic!(
                        "too short clause {} {:?}",
                        (cid as ClauseId).format(),
                        vec2int(&lits)
                    );
                }
                if self.watcher[lits[0].negate() as usize]
                    .iter()
                    .all(|w| w.c != cid as ClauseId)
                    || self.watcher[lits[1].negate() as usize]
                        .iter()
                        .all(|w| w.c != cid as ClauseId)
                {
                    panic!("watch broken");
                }
            }
        }
        true
    }
    #[allow(dead_code)]
    fn check_liveness2(&self) -> bool {
        let deads = self.watcher[NULL_LIT.negate() as usize]
            .iter()
            .map(|w| w.c)
            .collect::<Vec<ClauseId>>();
        for cid in 1..self.clause.len() {
            if self.clause[cid].is(Flag::DEAD) && !deads.contains(&(cid as ClauseId)) {
                panic!("done");
            }
            if !self.clause[cid].is(Flag::DEAD) {
                let lits = &self.clause[cid].lits;
                if lits.len() < 2 {
                    panic!(
                        "too short clause {} {:?}",
                        (cid as ClauseId).format(),
                        vec2int(&lits)
                    );
                }
                if self.watcher[lits[0].negate() as usize]
                    .iter()
                    .all(|w| w.c != cid as ClauseId)
                    || self.watcher[lits[1].negate() as usize]
                        .iter()
                        .all(|w| w.c != cid as ClauseId)
                {
                    panic!("watch broken");
                }
            }
        }
        for ws in &self.watcher[2..] {
            for w in ws {
                if self.clause[w.c as usize].is(Flag::DEAD) && !deads.contains(&w.c) {
                    panic!("done");
                }
            }
        }
        true
    }
    #[allow(dead_code)]
    fn check(&self) {
        let total = self.count(false);
        let nc = self.count(true);
        let nc2 = self.watcher.iter().skip(2).map(|v| v.count()).sum();
        if 2 * nc != nc2 {
            panic!("2 * {} != {}; total {}; alive {}", nc, nc2, total, nc);
        }
        let nd = total - nc;
        let nd2 = self.watcher[NULL_LIT.negate() as usize].len();
        if nd != nd2 {
            panic!("dead {} != {}; total {}; alive {}", nd, nd2, total, nc);
        }
    }
}
*/

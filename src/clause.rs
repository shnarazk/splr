use crate::assign::AssignStack;
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::state::{Stat, State};
use crate::traits::*;
use crate::types::*;
use crate::var::Var;
use std::cmp::Ordering;
use std::fmt;

const DB_INC_SIZE: usize = 200;
const CLA_ACTIVITY_MAX: f64 = 1e240;
const CLA_ACTIVITY_SCALE1: f64 = 1e-80;
const CLA_ACTIVITY_SCALE2: f64 = 1e-10;

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ClauseKind {
    Removable,
    Permanent,
    Binclause,
    Liftedlit,
}

impl ClauseIdIF for ClauseId {
    #[inline(always)]
    fn to_lit(self) -> Lit {
        (self & 0x0000_0000_FFFF_FFFF) as Lit
    }
    #[inline(always)]
    fn is_lifted_lit(self) -> bool {
        0 != 0x8000_0000_0000_0000 & self
    }
    fn format(self) -> String {
        if self == NULL_CLAUSE {
            "NullClause".to_string()
        } else {
            format!("C::{}", self)
        }
    }
}

pub struct Watch {
    pub blocker: Lit,
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
    fn initialize(mut self, n: usize) -> Self {
        if 2 <= n {
            self.push(Watch::default());
        }
        self
    }
    #[inline(always)]
    fn count(&self) -> usize {
        self[0].c
    }
    #[inline(always)]
    fn attach(&mut self, blocker: Lit, c: usize) {
        let next = self[0].c + 1;
        if next == self.len() {
            self.push(Watch { blocker, c });
        } else {
            self[next].blocker = blocker;
            self[next].c = c;
        }
        self[0].c = next;
    }
    #[inline(always)]
    fn detach(&mut self, n: usize) {
        let last = self[0].c;
        debug_assert!(0 < last);
        self.swap(n, last);
        self[last].c = NULL_CLAUSE;
        self[0].c -= 1;
    }
    #[inline(always)]
    fn detach_with(&mut self, cid: usize) {
        for n in 1..=self[0].c {
            if self[n].c == cid {
                self.detach(n);
                return;
            }
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ClauseFlag {
    Dead = 0,
    Learnt,
    JustUsed,
    Enqueued,
}

pub struct Clause {
    /// the literals
    pub lits: Vec<Lit>,
    /// LBD, NDD, or something, used by `reduce_db`
    pub rank: usize,
    /// clause activity used by `analyze` and `reduce_db`
    pub activity: f64,
    /// collection of bits
    flags: u16,
}

impl Default for Clause {
    fn default() -> Clause {
        Clause {
            flags: 0,
            lits: vec![],
            rank: 0,
            activity: 0.0,
        }
    }
}

impl ClauseIF for Clause {
    #[inline(always)]
    fn get_flag(&self, flag: ClauseFlag) -> bool {
        self.flags & (1 << flag as u16) != 0
    }
    #[inline(always)]
    fn flag_off(&mut self, flag: ClauseFlag) {
        self.flags &= !(1u16 << (flag as u16));
    }
    #[inline(always)]
    fn flag_on(&mut self, flag: ClauseFlag) {
        self.flags |= 1u16 << (flag as u16);
    }
    fn kill(&mut self, touched: &mut [bool]) {
        self.flag_on(ClauseFlag::Dead);
        debug_assert!(self.lits[0] != 0 && self.lits[1] != 0);
        touched[self.lits[0].negate() as usize] = true;
        touched[self.lits[1].negate() as usize] = true;
    }
}

impl Clause {
    #[allow(dead_code)]
    fn set_flag(&mut self, flag: ClauseFlag, val: bool) {
        if val {
            self.flags |= (val as u16) << (flag as u16);
        } else {
            self.flags &= !(1 << (flag as u16));
        }
    }
    fn map_flag<T>(&self, flag: ClauseFlag, a: T, b: T) -> T {
        if self.get_flag(flag) {
            a
        } else {
            b
        }
    }
}

impl PartialEq for Clause {
    #[inline(always)]
    fn eq(&self, other: &Clause) -> bool {
        self == other
    }
}

impl Eq for Clause {}

impl PartialOrd for Clause {
    #[inline(always)]
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
    #[inline(always)]
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

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "C{{{:?} {}{}}}",
            vec2int(&self.lits),
            self.map_flag(ClauseFlag::Dead, ", dead", ""),
            self.map_flag(ClauseFlag::Enqueued, ", enqueued", ""),
        )
    }
}

/// partition of clauses
pub struct ClauseDB {
    pub clause: Vec<Clause>,
    pub touched: Vec<bool>,
    pub watcher: Vec<Vec<Watch>>,
    pub num_active: usize,
    pub num_learnt: usize,
}

impl ClauseDBIF for ClauseDB {
    fn new(nv: usize, nc: usize) -> ClauseDB {
        let mut clause = Vec::with_capacity(1 + nc);
        clause.push(Clause::default());
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        let mut touched = Vec::with_capacity(2 * (nv + 1));
        for i in 0..2 * (nv + 1) {
            watcher.push(Vec::new().initialize(i));
            touched.push(false);
        }
        ClauseDB {
            clause,
            touched,
            watcher,
            num_active: 0,
            num_learnt: 0,
        }
    }
    fn garbage_collect(&mut self, vars: &mut [Var], elim: &mut Eliminator) {
        let ClauseDB {
            ref mut watcher,
            ref mut clause,
            ref mut touched,
            ..
        } = self;
        for (i, ws) in &mut watcher.iter_mut().enumerate().skip(2) {
            if !touched[i] {
                continue;
            }
            touched[i] = false;
            let mut n = 1;
            let n_max = ws.count();
            while n <= n_max {
                if clause[ws[n].c].get_flag(ClauseFlag::Dead) {
                    ws.detach(n);
                } else {
                    n += 1;
                }
            }
        }
        let recycled = &mut watcher[NULL_LIT.negate() as usize];
        for (ci, ch) in self.clause.iter_mut().enumerate().skip(1) {
            // the recycled clause is DEAD and EMPTY
            if ch.get_flag(ClauseFlag::Dead) && !ch.lits.is_empty() {
                recycled.push(Watch {
                    blocker: NULL_LIT,
                    c: ci,
                });
                if ch.get_flag(ClauseFlag::Learnt) {
                    self.num_learnt -= 1;
                }
                if elim.in_use {
                    for l in &ch.lits {
                        let vi = l.vi();
                        let v = &mut vars[vi];
                        if !v.eliminated {
                            if l.positive() {
                                v.pos_occurs.delete_unstable(|&cj| ci == cj);
                            } else {
                                v.neg_occurs.delete_unstable(|&cj| ci == cj);
                            }
                            elim.enqueue_var(v);
                        }
                    }
                }
                ch.lits.clear();
            }
        }
        self.num_active = self.clause.len() - recycled.len();
    }
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool) -> ClauseId {
        let cid;
        if let Some(w) = self.watcher[NULL_LIT.negate() as usize].pop() {
            cid = w.c;
            // debug_assert!(self.head[cid].get_flag(ClauseFlag::Dead));
            let ch = &mut self.clause[cid];
            self.watcher[v[0].negate() as usize].attach(v[1], cid);
            self.watcher[v[1].negate() as usize].attach(v[0], cid);
            ch.lits.clear();
            for l in v {
                ch.lits.push(*l);
            }
            ch.rank = rank;
            ch.flags = 0;
            if learnt {
                ch.flag_on(ClauseFlag::Learnt);
                self.num_learnt += 1;
            }
            ch.activity = 1.0;
        } else {
            let l0 = v[0];
            let l1 = v[1];
            let mut lits = Vec::with_capacity(v.len());
            for l in v {
                lits.push(*l);
            }
            cid = self.clause.len();
            let mut c = Clause {
                flags: 0,
                lits,
                rank,
                activity: 0.0,
            };
            if learnt {
                c.flag_on(ClauseFlag::Learnt);
                self.num_learnt += 1;
            }
            self.clause.push(c);
            self.watcher[l0.negate() as usize].attach(l1, cid);
            self.watcher[l1.negate() as usize].attach(l0, cid);
        };
        self.num_active += 1;
        cid
    }
    fn reset_lbd(&mut self, vars: &[Var], temp: &mut [usize]) {
        let mut key = temp[0];
        for ch in &mut self.clause[1..] {
            if ch.get_flag(ClauseFlag::Dead) {
                continue;
            }
            key += 1;
            let mut cnt = 0;
            for l in &ch.lits {
                let lv = vars[l.vi()].level;
                if temp[lv] != key && lv != 0 {
                    temp[lv] = key;
                    cnt += 1;
                }
            }
            ch.rank = cnt;
        }
        temp[0] = key + 1;
    }
    fn bump_activity(&mut self, inc: &mut f64, cid: ClauseId, _d: f64) {
        let c = &mut self.clause[cid];
        let a = c.activity + *inc;
        // a = (c.activity + d) / 2.0;
        c.activity = a;
        if CLA_ACTIVITY_MAX < a {
            for c in &mut self.clause[1..] {
                if c.get_flag(ClauseFlag::Learnt) {
                    c.activity *= CLA_ACTIVITY_SCALE1;
                }
            }
            *inc *= CLA_ACTIVITY_SCALE2;
        }
    }
    fn count(&self, alive: bool) -> usize {
        if alive {
            self.clause.len() - self.watcher[NULL_LIT.negate() as usize].len() - 1
        } else {
            self.clause.len() - 1
        }
    }
    /// renamed from newLearntClause
    // Note: set lbd to 0 if you want to add the clause to Permanent.
    fn add_clause(
        &mut self,
        config: &mut Config,
        elim: &mut Eliminator,
        vars: &mut [Var],
        v: &mut Vec<Lit>,
        lbd: usize,
    ) -> ClauseId {
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
        let kind = if lbd == 0 && elim.in_use {
            ClauseKind::Permanent
        } else if v.len() == 2 {
            ClauseKind::Binclause
        } else if (config.use_chan_seok && lbd <= config.co_lbd_bound) || lbd == 0 {
            ClauseKind::Permanent
        } else {
            ClauseKind::Removable
        };
        let cid = self.new_clause(&v, lbd, kind == ClauseKind::Removable);
        let ch = &mut self.clause[cid];
        ch.activity = config.var_inc;
        vars.attach_clause(elim, cid, ch, true);
        cid
    }
    /// called from strengthen_clause, backward_subsumption_check, eliminate_var, substitute
    fn remove_clause(&mut self, cid: ClauseId) {
        let ch = &mut self.clause[cid];
        debug_assert!(!ch.get_flag(ClauseFlag::Dead));
        ch.flag_on(ClauseFlag::Dead);
        if ch.lits.is_empty() {
            return;
        }
        let w0 = ch.lits[0].negate();
        if 1 < ch.lits.len() {
            let w1 = ch.lits[1].negate();
            debug_assert_ne!(w0, w1);
            self.touched[w1 as usize] = true;
        }
        self.touched[w0 as usize] = true;
    }
    fn reduce(&mut self, elim: &mut Eliminator, state: &mut State, vars: &mut [Var]) {
        self.reset_lbd(vars, &mut state.lbd_temp);
        let ClauseDB {
            ref mut clause,
            ref mut touched,
            ..
        } = self;
        let mut perm = Vec::with_capacity(clause.len());
        for (i, b) in clause.iter().enumerate().skip(1) {
            if b.get_flag(ClauseFlag::Learnt) && !b.get_flag(ClauseFlag::Dead) && !vars.locked(b, i)
            {
                perm.push(i);
            }
        }
        if perm.is_empty() {
            return;
        }
        perm.sort_by(|&a, &b| clause[a].cmp(&clause[b]));
        let keep = perm.len() / 2;
        if clause[perm[keep]].rank <= 5 {
            state.next_reduction += 1000;
        };
        for i in &perm[keep..] {
            let c = &mut clause[*i];
            if c.get_flag(ClauseFlag::JustUsed) {
                c.flag_off(ClauseFlag::JustUsed)
            } else {
                c.kill(touched);
            }
        }
        self.garbage_collect(vars, elim);
        state.next_reduction += DB_INC_SIZE;
        state.stats[Stat::Reduction as usize] += 1;
    }
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut Config,
        elim: &mut Eliminator,
        state: &mut State,
        vars: &mut [Var],
    ) -> bool {
        self.reset_lbd(vars, &mut state.lbd_temp);
        debug_assert_eq!(asgs.level(), 0);
        // reset reason since decision level is zero.
        for v in &mut vars[1..] {
            v.reason = NULL_CLAUSE;
        }
        if elim.in_use {
            elim.eliminate(asgs, config, self, state, vars);
            if !state.ok {
                return false;
            }
        }
        for c in &mut self.clause[1..] {
            if !c.get_flag(ClauseFlag::Dead) && vars.satisfies(&c.lits) {
                c.kill(&mut self.touched);
                if elim.in_use {
                    for l in &c.lits {
                        let v = &mut vars[l.vi()];
                        if !v.eliminated {
                            elim.enqueue_var(v);
                        }
                    }
                }
            }
        }
        self.garbage_collect(vars, elim);
        state.stats[Stat::Simplification as usize] += 1;
        true
    }
}

impl ClauseDB {
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

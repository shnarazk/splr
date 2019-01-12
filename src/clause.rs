#![allow(unused_variables)]
use crate::assign::AssignStack;
use crate::config::SolverConfig;
use crate::eliminator::Eliminator;
use crate::state::{SolverState, Stat};
use crate::traits::*;
use crate::types::*;
use crate::var::Var;
use std::cmp::Ordering;
use std::fmt;

const CLAUSE_INDEX_BITS: usize = 60;
const CLAUSE_INDEX_MASK: usize = 0x0FFF_FFFF_FFFF_FFFF;
const DB_INC_SIZE: usize = 200;
const CLA_ACTIVITY_MAX: f64 = 1e240;
const CLA_ACTIVITY_SCALE1: f64 = 1e-80;
const CLA_ACTIVITY_SCALE2: f64 = 1e-10;

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ClauseKind {
    Liftedlit,
    Removable,
    Permanent,
    Binclause,
    Uniclause,
}

impl ClauseKind {
    #[inline(always)]
    fn tag(self) -> usize {
        match self {
            ClauseKind::Liftedlit => 0x0000_0000_0000_0000,
            ClauseKind::Removable => 0x1000_0000_0000_0000,
            ClauseKind::Permanent => 0x2000_0000_0000_0000,
            ClauseKind::Binclause => 0x3000_0000_0000_0000,
            ClauseKind::Uniclause => 0x4000_0000_0000_0000,
        }
    }
}

/// Clause Index, not ID because it's used only within a Vec<Clause>
pub type ClauseIndex = usize;

impl ClauseIdIF for ClauseId {
    #[inline(always)]
    fn from_(kind: ClauseKind, cix: ClauseIndex) -> ClauseId {
        kind.tag() | cix
    }
    #[inline(always)]
    fn to_index(&self) -> ClauseIndex {
        *self & CLAUSE_INDEX_MASK
    }
    #[inline(always)]
    fn to_kind(&self) -> usize {
        *self >> CLAUSE_INDEX_BITS
    }
    #[inline(always)]
    fn is(&self, kind: ClauseKind, ix: ClauseIndex) -> bool {
        self.to_kind() == kind as usize && self.to_index() == ix
    }
    fn format(&self) -> String {
        match self.to_kind() {
            _ if *self == 0 => "NullClause".to_string(),
            0 => format!("Lifted::{}", self.to_index()),
            1 => format!("Learnt::{}", self.to_index()),
            2 => format!("Perman::{}", self.to_index()),
            3 => format!("Binary::{}", self.to_index()),
            4 => format!("Unicls::{}", self.to_index()),
            _ => format!("Ilegal::{}", self.to_index()),
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

impl Watch {
    fn new(blocker: Lit, c: ClauseId) -> Watch {
        Watch { blocker, c }
    }
}

impl WatchManagement for Vec<Watch> {
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
    fn detach_with(&mut self, cix: usize) {
        for n in 1..=self[0].c {
            if self[n].c == cix {
                self.detach(n);
                return;
            }
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ClauseFlag {
    Dead = 0,
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
pub struct ClausePartition {
    pub kind: ClauseKind,
    pub tag: usize,
    pub head: Vec<Clause>,
    pub touched: Vec<bool>,
    pub watcher: Vec<Vec<Watch>>,
}

impl ClausePartitionIF for ClausePartition {
    fn build(kind: ClauseKind, nv: usize, nc: usize) -> ClausePartition {
        let mut head = Vec::with_capacity(1 + nc);
        head.push(Clause::default());
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        let mut touched = Vec::with_capacity(2 * (nv + 1));
        for i in 0..2 * (nv + 1) {
            watcher.push(Vec::new().initialize(i));
            touched.push(false);
        }
        ClausePartition {
            kind,
            tag: kind.tag(),
            head,
            touched,
            watcher,
        }
    }
    fn garbage_collect(&mut self, vars: &mut [Var], elim: &mut Eliminator) {
        let ClausePartition {
            ref mut watcher,
            ref mut head,
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
                if head[ws[n].c].get_flag(ClauseFlag::Dead) {
                    ws.detach(n);
                } else {
                    n += 1;
                }
            }
        }
        let recycled = &mut watcher[NULL_LIT.negate() as usize];
        for (ci, ch) in self.head.iter_mut().enumerate().skip(1) {
            // the recycled clause is DEAD and EMPTY
            if ch.get_flag(ClauseFlag::Dead) && !ch.lits.is_empty() {
                recycled.push(Watch::new(NULL_LIT, ci));
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
    }
    fn new_clause(&mut self, v: &[Lit], rank: usize) -> ClauseId {
        let cix;
        if let Some(w) = self.watcher[NULL_LIT.negate() as usize].pop() {
            cix = w.c;
            // debug_assert!(self.head[cix].get_flag(ClauseFlag::Dead));
            let ch = &mut self.head[cix];
            self.watcher[v[0].negate() as usize].attach(v[1], cix);
            self.watcher[v[1].negate() as usize].attach(v[0], cix);
            ch.lits.clear();
            for l in v {
                ch.lits.push(*l);
            }
            ch.rank = rank;
            ch.flags = 0;
            ch.activity = 1.0;
        } else {
            let l0 = v[0];
            let l1 = v[1];
            let mut lits = Vec::with_capacity(v.len());
            for l in v {
                lits.push(*l);
            }
            cix = self.head.len();
            self.head.push(Clause {
                flags: 0,
                lits,
                rank,
                activity: 0.0,
            });
            self.watcher[l0.negate() as usize].attach(l1, cix);
            self.watcher[l1.negate() as usize].attach(l0, cix);
        };
        ClauseId::from_(self.kind, cix)
    }
    fn reset_lbd(&mut self, vars: &[Var], temp: &mut [usize]) {
        let mut key = temp[0];
        for ch in &mut self.head[1..] {
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
    fn bump_activity(&mut self, inc: &mut f64, cix: ClauseIndex, _d: f64) {
        let c = &mut self.head[cix];
        let a = c.activity + *inc;
        // a = (c.activity + d) / 2.0;
        c.activity = a;
        if CLA_ACTIVITY_MAX < a {
            for c in &mut self.head[1..] {
                c.activity *= CLA_ACTIVITY_SCALE1;
            }
            *inc *= CLA_ACTIVITY_SCALE2;
        }
    }
    fn count(&self, alive: bool) -> usize {
        if alive {
            self.head.len() - self.watcher[NULL_LIT.negate() as usize].len() - 1
        } else {
            self.head.len() - 1
        }
    }
}

impl ClausePartition {
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

pub type ClauseDB = [ClausePartition; 4];

impl ClauseDBIF for ClauseDB {
    fn new(nv: usize, nc: usize) -> ClauseDB {
        [
            ClausePartition::build(ClauseKind::Liftedlit, nv, 0),
            ClausePartition::build(ClauseKind::Removable, nv, nc),
            ClausePartition::build(ClauseKind::Permanent, nv, 256),
            ClausePartition::build(ClauseKind::Binclause, nv, 256),
        ]
    }
    /// renamed from newLearntClause
    // Note: set lbd to 0 if you want to add the clause to Permanent.
    fn add_clause(
        &mut self,
        config: &mut SolverConfig,
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
        let cid = self[kind as usize].new_clause(&v, lbd);
        let ch = clause_mut!(*self, cid);
        ch.activity = config.var_inc;
        vars.attach_clause(elim, cid, ch, false);
        cid
    }
    /// 4. removeClause
    /// called from strengthen_clause, backward_subsumption_check, eliminate_var, substitute
    fn remove_clause(&mut self, cid: ClauseId) {
        let ch = clause_mut!(*self, cid);
        debug_assert!(!ch.get_flag(ClauseFlag::Dead));
        ch.flag_on(ClauseFlag::Dead);
        if ch.lits.is_empty() {
            return;
        }
        let w0 = ch.lits[0].negate();
        if 1 < ch.lits.len() {
            let w1 = ch.lits[1].negate();
            debug_assert_ne!(w0, w1);
            self[cid.to_kind()].touched[w1 as usize] = true;
        }
        self[cid.to_kind()].touched[w0 as usize] = true;
    }
    fn reduce(&mut self, elim: &mut Eliminator, state: &mut SolverState, vars: &mut [Var]) {
        self[ClauseKind::Removable as usize].reset_lbd(vars, &mut state.lbd_temp);
        let ClausePartition {
            ref mut head,
            ref mut touched,
            ..
        } = &mut self[ClauseKind::Removable as usize];
        let mut perm = Vec::with_capacity(head.len());
        for (i, b) in head.iter().enumerate().skip(1) {
            if !b.get_flag(ClauseFlag::Dead)
                && !vars.locked(b, ClauseId::from_(ClauseKind::Removable, i))
            {
                perm.push(i);
            }
        }
        if perm.is_empty() {
            return;
        }
        perm.sort_by(|&a, &b| head[a].cmp(&head[b]));
        let keep = perm.len() / 2;
        if head[perm[keep]].rank <= 5 {
            state.next_reduction += 1000;
        };
        for i in &perm[keep..] {
            let ch = &mut head[*i];
            if ch.get_flag(ClauseFlag::JustUsed) {
                ch.flag_off(ClauseFlag::JustUsed)
            } else {
                ch.flag_on(ClauseFlag::Dead);
                debug_assert!(ch.lits[0] != 0 && ch.lits[1] != 0);
                touched[ch.lits[0].negate() as usize] = true;
                touched[ch.lits[1].negate() as usize] = true;
            }
        }
        self[ClauseKind::Removable as usize].garbage_collect(vars, elim);
        state.next_reduction += DB_INC_SIZE;
        state.stats[Stat::Reduction as usize] += 1;
    }
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut SolverConfig,
        elim: &mut Eliminator,
        state: &mut SolverState,
        vars: &mut [Var],
    ) -> bool {
        self[ClauseKind::Removable as usize].reset_lbd(vars, &mut state.lbd_temp);
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
        for ck in &mut self[ClauseKind::Liftedlit as usize..=ClauseKind::Binclause as usize] {
            for ch in &mut ck.head[1..] {
                if !ch.get_flag(ClauseFlag::Dead) && vars.satisfies(&ch.lits) {
                    debug_assert!(ch.lits[0] != 0 && ch.lits[1] != 0);
                    ch.flag_on(ClauseFlag::Dead);
                    ck.touched[ch.lits[0].negate() as usize] = true;
                    ck.touched[ch.lits[1].negate() as usize] = true;
                    if elim.in_use {
                        for l in &ch.lits {
                            let v = &mut vars[l.vi()];
                            if !v.eliminated {
                                elim.enqueue_var(v);
                            }
                        }
                    }
                }
            }
            ck.garbage_collect(vars, elim);
        }
        state.stats[Stat::Simplification as usize] += 1;
        true
    }
}

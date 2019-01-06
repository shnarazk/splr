#![allow(unused_variables)]
use crate::assign::*;
use crate::config::SolverConfiguration;
use crate::eliminator::*;
use crate::state::*;
use crate::types::*;
use crate::var::{Var, VarManagement};
use std::cmp::Ordering;
use std::f64;
use std::fmt;

/// For ClauseDB
pub trait ClauseManagement {
    fn add_clause(
        &mut self,
        config: &mut SolverConfiguration,
        eliminator: &mut Eliminator,
        vars: &mut [Var],
        v: &mut Vec<Lit>,
        lbd: usize,
        act: f64,
    ) -> ClauseId;
    fn remove_clause(&mut self, cid: ClauseId);
    fn change_clause_kind(
        &mut self,
        eliminator: &mut Eliminator,
        vars: &mut [Var],
        cid: ClauseId,
        kind: ClauseKind,
    );
    fn reduce(&mut self, eliminator: &mut Eliminator, state: &mut SolverState, vars: &mut [Var]);
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut SolverConfiguration,
        eliminator: &mut Eliminator,
        state: &mut SolverState,
        vars: &mut [Var],
    ) -> bool;
}

/// For Vec<Watch>
pub trait WatchManagement {
    fn initialize(self, n: usize) -> Self;
    fn count(&self) -> usize;
    fn attach(&mut self, blocker: Lit, c: usize);
    fn detach(&mut self, n: usize);
    fn detach_with(&mut self, cix: usize);
}

/// For usize
pub trait ClauseIdIndexEncoding {
    fn to_id(&self) -> ClauseId;
    fn to_index(&self) -> ClauseIndex;
    fn to_kind(&self) -> usize;
    fn is(&self, kind: ClauseKind, ix: ClauseIndex) -> bool;
}

pub type ClauseDB = [ClausePartition; 4];

const DB_INC_SIZE: usize = 200;

/// Clause Index, not ID because it's used only within a Vec<Clause>
pub type ClauseIndex = usize;

pub struct Watch {
    pub blocker: Lit,
    pub c: ClauseId,
}

impl Watch {
    pub fn new(blocker: Lit, c: ClauseId) -> Watch {
        Watch { blocker, c }
    }
}

pub struct ClauseHead {
    /// collection of bits
    pub flags: u16,
    /// the literals
    pub lits: Vec<Lit>,
    /// LBD, NDD, or something, used by `reduce_db`
    pub rank: usize,
    /// clause activity used by `analyze` and `reduce_db`
    pub activity: f64,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ClauseFlag {
    Kind0 = 0,
    Kind1,
    Dead,
    JustUsed,
    Enqueued,
}

/// partition of clauses
pub struct ClausePartition {
    pub kind: ClauseKind,
    pub tag: usize,
    pub init_size: usize,
    pub head: Vec<ClauseHead>,
    pub perm: Vec<ClauseIndex>,
    pub touched: Vec<bool>,
    pub watcher: Vec<Vec<Watch>>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ClauseKind {
    Liftedlit,
    Removable,
    Permanent,
    Binclause,
    Uniclause,
}

const CLAUSE_INDEX_BITS: usize = 60;
const CLAUSE_INDEX_MASK: usize = 0x0FFF_FFFF_FFFF_FFFF;

impl ClauseKind {
    #[inline(always)]
    pub fn tag(self) -> usize {
        match self {
            ClauseKind::Liftedlit => 0x0000_0000_0000_0000,
            ClauseKind::Removable => 0x1000_0000_0000_0000,
            ClauseKind::Permanent => 0x2000_0000_0000_0000,
            ClauseKind::Binclause => 0x3000_0000_0000_0000,
            ClauseKind::Uniclause => 0x4000_0000_0000_0000,
        }
    }
    #[inline(always)]
    pub fn mask(self) -> usize {
        CLAUSE_INDEX_MASK
    }
    #[inline(always)]
    pub fn id_from(self, cix: ClauseIndex) -> ClauseId {
        cix | self.tag()
    }
    #[inline(always)]
    pub fn index_from(self, cid: ClauseId) -> ClauseIndex {
        cid & CLAUSE_INDEX_MASK
    }
}

impl ClausePartition {
    pub fn build(kind: ClauseKind, nv: usize, nc: usize) -> ClausePartition {
        let mut head = Vec::with_capacity(1 + nc);
        head.push(ClauseHead {
            flags: 0,
            lits: vec![],
            rank: 0,
            activity: 0.0,
        });
        let mut perm = Vec::with_capacity(1 + nc);
        perm.push(NULL_CLAUSE);
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        let mut touched = Vec::with_capacity(2 * (nv + 1));
        for i in 0..2 * (nv + 1) {
            watcher.push(Vec::new().initialize(i));
            touched.push(false);
        }
        ClausePartition {
            kind,
            tag: kind.tag(),
            init_size: nc,
            head,
            perm,
            touched,
            watcher,
        }
    }
    #[inline(always)]
    pub fn id_from(&self, cix: ClauseIndex) -> ClauseId {
        cix | self.tag
    }
    #[inline(always)]
    pub fn index_from(&self, cid: ClauseId) -> ClauseIndex {
        cid & CLAUSE_INDEX_MASK
    }
}

impl ClauseHead {
    #[inline(always)]
    pub fn get_kind(&self) -> ClauseKind {
        match self.flags & 3 {
            0 => ClauseKind::Removable,
            1 => ClauseKind::Permanent,
            2 => ClauseKind::Binclause,
            _ => panic!("impossible clause kind"),
        }
    }
    #[inline(always)]
    pub fn flag_off(&mut self, flag: ClauseFlag) {
        self.flags &= !(1u16 << (flag as u16));
    }
    #[inline(always)]
    pub fn flag_on(&mut self, flag: ClauseFlag) {
        self.flags |= 1u16 << (flag as u16);
    }
    #[inline(always)]
    pub fn set_flag(&mut self, flag: ClauseFlag, val: bool) {
        if val {
            self.flags |= (val as u16) << (flag as u16);
        } else {
            self.flags &= !(1 << (flag as u16));
        }
    }
    #[inline(always)]
    pub fn get_flag(&self, flag: ClauseFlag) -> bool {
        self.flags & (1 << flag as u16) != 0
    }
}

impl ClauseFlag {
    #[allow(dead_code)]
    fn as_bit(self, val: bool) -> u16 {
        (val as u16) << (self as u16)
    }
}

impl ClauseIdIndexEncoding for usize {
    #[inline(always)]
    fn to_id(&self) -> ClauseId {
        *self
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
        (*self).to_kind() == kind as usize && (*self).to_index() == ix
    }
}

impl PartialEq for ClauseHead {
    #[inline(always)]
    fn eq(&self, other: &ClauseHead) -> bool {
        self == other
    }
}

impl Eq for ClauseHead {}

impl PartialOrd for ClauseHead {
    #[inline(always)]
    fn partial_cmp(&self, other: &ClauseHead) -> Option<Ordering> {
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

impl Ord for ClauseHead {
    #[inline(always)]
    fn cmp(&self, other: &ClauseHead) -> Ordering {
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

impl fmt::Display for ClauseHead {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "C{{{:?} {}{}{}}}",
            vec2int(&self.lits),
            match self.flags & 3 {
                0 => 'L',
                1 => 'R',
                2 => 'P',
                3 => 'B',
                _ => '?',
            },
            if self.get_flag(ClauseFlag::Dead) {
                ", dead"
            } else {
                ""
            },
            if self.get_flag(ClauseFlag::Enqueued) {
                ", enqueued"
            } else {
                ""
            },
        )
    }
}

pub fn cid2fmt(cid: ClauseId) -> String {
    match cid.to_kind() {
        0 if cid == 0 => "NullClause".to_string(),
        0 => format!("Lifted::{}", cid.to_index()),
        1 => format!("Learnt::{}", cid.to_index()),
        2 => format!("Perman::{}", cid.to_index()),
        3 => format!("Binary::{}", cid.to_index()),
        4 => format!("Unicls::{}", cid.to_index()),
        _ => format!("Ilegal::{}", cid.to_index()),
    }
}

pub struct ClauseIter<'a> {
    body: &'a ClauseHead,
    end: usize,
    index: usize,
}

pub fn clause_iter(cb: &ClauseHead) -> ClauseIter {
    ClauseIter {
        body: cb,
        end: cb.lits.len(),
        index: 0,
    }
}

impl<'a> Iterator for ClauseIter<'a> {
    type Item = Lit;
    fn next(&mut self) -> Option<Lit> {
        if self.index < self.end {
            let l = self.body.lits[self.index];
            self.index += 1;
            Some(l)
        } else {
            None
        }
    }
}

impl ClausePartition {
    pub fn garbage_collect(&mut self, vars: &mut [Var], eliminator: &mut Eliminator) {
        let ClausePartition {
            ref mut watcher,
            ref mut head,
            ref mut touched,
            ..
        } = self;
        for (i, ws) in &mut watcher.iter_mut().enumerate().skip(2) {
            if touched[i] {
                touched[i] = false;
            } else {
                continue;
            }
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
                if eliminator.use_elim {
                    for l in &ch.lits {
                        let vi = l.vi();
                        let v = &mut vars[vi];
                        if !v.eliminated {
                            if l.positive() {
                                v.pos_occurs.delete_unstable(|&cj| ci == cj);
                            } else {
                                v.neg_occurs.delete_unstable(|&cj| ci == cj);
                            }
                            eliminator.enqueue_var(v);
                        }
                    }
                }
                ch.lits.clear();
            }
        }
        // self.check();
    }
    pub fn new_clause(&mut self, v: &[Lit], rank: usize) -> ClauseId {
        let cix;
        if let Some(w) = self.watcher[NULL_LIT.negate() as usize].pop() {
            cix = w.c;
            // debug_assert!(self.head[cix].get_flag(ClauseFlag::Dead));
            let ch = &mut self.head[cix];
            self.watcher[v[0].negate() as usize].attach(v[1], cix);
            self.watcher[v[1].negate() as usize].attach(v[0], cix);
            ch.lits.clear();
            for l in &v[..] {
                ch.lits.push(*l);
            }
            ch.rank = rank;
            ch.flags = self.kind as u16; // reset Dead, JustUsed, and Touched
            ch.activity = 1.0;
        } else {
            let l0 = v[0];
            let l1 = v[1];
            let mut lits = Vec::with_capacity(v.len());
            for l in &v[..] {
                lits.push(*l);
            }
            cix = self.head.len();
            let w0 = l0.negate() as usize;
            let w1 = l1.negate() as usize;
            self.head.push(ClauseHead {
                flags: self.kind as u16,
                lits,
                rank,
                activity: 1.0,
            });
            self.perm.push(cix);
            self.watcher[w0].attach(l1, cix);
            self.watcher[w1].attach(l0, cix);
        };
        self.id_from(cix)
    }
    fn reset_lbd(&mut self, vars: &[Var], temp: &mut [usize]) {
        let mut key = temp[0];
        for i in 1..self.head.len() {
            let ch = &mut self.head[i];
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
    pub fn bump_activity(&mut self, cix: ClauseIndex, val: f64, cla_inc: &mut f64) {
        let c = &mut self.head[cix];
        let a = c.activity + *cla_inc;
        // a = (c.activity + val) / 2.0;
        c.activity = a;
        if 1.0e20 < a {
            for c in self.head.iter_mut().skip(1) {
                if 1.0e-300 < c.activity {
                    c.activity *= 1.0e-20;
                }
            }
            *cla_inc *= 1.0e-20;
        }
    }
    pub fn count(&self, alive: bool) -> usize {
        if alive {
            self.head.len() - self.watcher[NULL_LIT.negate() as usize].len() - 1
        } else {
            self.head.len() - 1
        }
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

impl ClauseManagement for ClauseDB {
    /// renamed from newLearntClause
    // Note: set lbd to 0 if you want to add the clause to Permanent.
    fn add_clause(
        &mut self,
        config: &mut SolverConfiguration,
        eliminator: &mut Eliminator,
        vars: &mut [Var],
        v: &mut Vec<Lit>,
        lbd: usize,
        act: f64,
    ) -> ClauseId {
        debug_assert!(1 < v.len());
        // let lbd = v.lbd(&self.vars, &mut self.lbd_temp);
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
        let kind = if lbd == 0 && eliminator.use_elim {
            ClauseKind::Permanent
        } else if v.len() == 2 {
            ClauseKind::Binclause
        } else if (config.use_chan_seok && lbd <= config.co_lbd_bound) || lbd == 0 {
            ClauseKind::Permanent
        } else {
            ClauseKind::Removable
        };
        let cid = self[kind as usize].new_clause(&v, lbd);
        // self.bump_cid(cid);
        if cid.to_kind() == ClauseKind::Removable as usize {
            self[ClauseKind::Removable as usize].bump_activity(
                cid.to_index(),
                act,
                &mut config.cla_inc,
            );
        }
        let ch = clause_mut!(*self, cid);
        vars.attach_clause(cid, ch, false, eliminator);
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
    // This should be called at DL == 0.
    fn change_clause_kind(
        &mut self,
        eliminator: &mut Eliminator,
        vars: &mut [Var],
        cid: ClauseId,
        kind: ClauseKind,
    ) {
        // let dl = self.decision_level();
        // debug_assert_eq!(dl, 0);
        let ch = clause_mut!(*self, cid);
        if ch.get_flag(ClauseFlag::Dead) {
            return;
        }
        ch.flag_on(ClauseFlag::Dead);
        let mut vec = Vec::new();
        for x in &ch.lits {
            vec.push(*x);
        }
        let r = ch.rank;
        let w0 = ch.lits[0].negate() as usize;
        let w1 = ch.lits[1].negate() as usize;
        self[kind as usize].new_clause(&vec, r);
        self[cid.to_kind()].touched[w0] = true;
        self[cid.to_kind()].touched[w1] = true;
    }
    fn reduce(&mut self, eliminator: &mut Eliminator, state: &mut SolverState, vars: &mut [Var]) {
        self[ClauseKind::Removable as usize].reset_lbd(vars, &mut state.lbd_temp[..]);
        let ClausePartition {
            ref mut head,
            ref mut touched,
            ref mut perm,
            ..
        } = &mut self[ClauseKind::Removable as usize];
        let mut nc = 1;
        for (i, b) in head.iter().enumerate().skip(1) {
            if !b.get_flag(ClauseFlag::Dead) && !vars.locked(b, ClauseKind::Removable.id_from(i)) {
                perm[nc] = i;
                nc += 1;
            }
        }
        perm[1..nc].sort_by(|&a, &b| head[a].cmp(&head[b]));
        let keep = nc / 2;
        if head[perm[keep]].rank <= 5 {
            state.next_reduction += 1000;
        };
        for i in keep..nc {
            let ch = &mut head[perm[i]];
            if ch.get_flag(ClauseFlag::JustUsed) {
                ch.flag_off(ClauseFlag::JustUsed)
            } else {
                ch.flag_on(ClauseFlag::Dead);
                debug_assert!(ch.lits[0] != 0 && ch.lits[1] != 0);
                touched[ch.lits[0].negate() as usize] = true;
                touched[ch.lits[1].negate() as usize] = true;
            }
        }
        self[ClauseKind::Removable as usize].garbage_collect(vars, eliminator);
        state.next_reduction += DB_INC_SIZE;
        state.stats[Stat::Reduction as usize] += 1;
    }
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut SolverConfiguration,
        eliminator: &mut Eliminator,
        state: &mut SolverState,
        vars: &mut [Var],
    ) -> bool {
        self[ClauseKind::Removable as usize].reset_lbd(vars, &mut state.lbd_temp);
        debug_assert_eq!(asgs.level(), 0);
        // reset reason since decision level is zero.
        for v in &mut vars[1..] {
            if v.reason != NULL_CLAUSE {
                v.reason = NULL_CLAUSE;
            }
        }
        if eliminator.use_elim
        // && state.stats[Stat::Simplification as usize] % 8 == 0
        // && state.eliminator.last_invocatiton < self.stats[Stat::Reduction as usize] as usize
        {
            eliminator.eliminate(asgs, config, self, state, vars);
            eliminator.last_invocatiton = state.stats[Stat::Reduction as usize] as usize;
            if !state.ok {
                return false;
            }
        }
        {
            for ck in &mut self[ClauseKind::Liftedlit as usize..=ClauseKind::Binclause as usize] {
                for ch in &mut ck.head[1..] {
                    if !ch.get_flag(ClauseFlag::Dead) && vars.satisfies(&ch.lits) {
                        ch.flag_on(ClauseFlag::Dead);
                        debug_assert!(ch.lits[0] != 0 && ch.lits[1] != 0);
                        ck.touched[ch.lits[0].negate() as usize] = true;
                        ck.touched[ch.lits[1].negate() as usize] = true;
                        if eliminator.use_elim {
                            for l in &ch.lits {
                                let v = &mut (*vars)[l.vi()];
                                if !v.eliminated {
                                    eliminator.enqueue_var(v);
                                }
                            }
                        }
                    }
                }
                ck.garbage_collect(vars, eliminator);
            }
        }
        state.stats[Stat::Simplification as usize] += 1;
        // self.check_eliminator();
        true
    }
}

impl WatchManagement for Vec<Watch> {
    fn initialize(mut self, n: usize) -> Self {
        if 2 <= n {
            self.push(Watch {
                blocker: NULL_LIT,
                c: 0,
            });
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
        let mut n = 1;
        let n_max = self[0].c;
        while n <= n_max {
            if self[n].c == cix {
                self.detach(n);
                return;
            }
            n += 1;
        }
    }
}

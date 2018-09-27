use eliminator::ClauseElimination;
use solver::{SearchStrategy, Solver, Stat, CDCL, CO_LBD_BOUND};
use std::cmp::Ordering;
use std::f64;
use std::fmt;
use types::*;
use var::{Satisfiability, Var};

/// for ClausePartition
pub trait GC {
    fn garbage_collect(&mut self) -> ();
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool, locked: bool) -> ClauseId;
    fn reset_lbd(&mut self, vars: &[Var]) -> ();
    fn move_to(&mut self, list: &mut ClauseId, ci: ClauseIndex, index: usize) -> ClauseIndex;
}

/// for usize
pub trait ClauseIdIndexEncoding {
    fn to_id(&self) -> ClauseId;
    fn to_index(&self) -> ClauseIndex;
    fn to_kind(&self) -> usize;
}

/// for Solver
pub trait ClauseManagement {
    fn bump_cid(&mut self, ci: ClauseId) -> ();
    fn decay_cla_activity(&mut self) -> ();
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
    fn add_clause(&mut self, v: &mut Vec<Lit>, lbd: usize) -> ClauseId;
    fn reduce(&mut self) -> ();
    fn simplify(&mut self) -> bool;
    fn lbd_of_an_learnt_lits(&mut self) -> usize;
    fn lbd_of(&mut self, cid: ClauseId) -> usize;
    fn biclause_subsume(&mut self, c: &ClauseHead) -> ();
    fn num_literals(&self, cid: ClauseIndex) -> usize;
}

const DB_INC_SIZE: usize = 200;

pub const CLAUSE_KINDS: [ClauseKind; 3] = [
    ClauseKind::Removable,
    ClauseKind::Permanent,
    ClauseKind::Binclause,
];

pub const RANK_NULL: usize = 0; // for NULL_CLAUSE
pub const RANK_CONST: usize = 1; // for given clauses
pub const RANK_NEED: usize = 2; // for newly generated bi-clauses

/// Clause Index, not ID because it's used only within a Vec<Clause>
pub type ClauseIndex = usize;

#[derive(Clone, Copy, Debug)]
pub struct ClauseHead {
    /// The first two literals
    pub lit: [Lit; 2],
    /// the literals without lit0 and lit1
    pub next_watcher: [usize; 2],
}

/// Clause
#[derive(Debug)]
pub struct ClauseBody {
    /// collection of bits
    pub flag: u16,
    /// the remaining literals
    pub lits: Vec<Lit>,
    /// LBD or NDD and so on, used by `reduce_db`
    pub rank: usize,
    /// clause activity used by `analyze` and `reduce_db`
    pub activity: f64,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum ClauseFlag {
    Kind0 = 0,
    Kind1,
    Dead,
    Locked,
    Learnt,
    JustUsed,
    SveMark,                    // TODO need?
    Queued,                     // TODO need?
    Touched,
}

/// partition of clauses
#[derive(Debug)]
pub struct ClausePartition {
    pub kind: ClauseKind,
    pub init_size: usize,
    pub head: Vec<ClauseHead>,
    pub body: Vec<ClauseBody>,
    pub touched: Vec<bool>,
    pub watcher: Vec<ClauseIndex>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClauseKind {
    Removable = 0,
    Permanent,
    Binclause,
}

const CLAUSE_INDEX_BITS: usize = 60;
const CLAUSE_INDEX_MASK: usize = 0x0FFF_FFFF_FFFF_FFFF;

impl ClauseKind {
    pub fn tag(self) -> usize {
        match self {
            ClauseKind::Removable => 0x0000_0000_0000_0000,
            ClauseKind::Permanent => 0x1000_0000_0000_0000,
            ClauseKind::Binclause => 0x2000_0000_0000_0000,
        }
    }
    pub fn mask(self) -> usize {
        CLAUSE_INDEX_MASK
    }
    pub fn id_from(self, cix: ClauseIndex) -> ClauseId {
        cix | self.tag()
    }
    pub fn index_from(self, cid: ClauseId) -> ClauseIndex {
        cid & self.mask()
    }
}

impl ClausePartition {
    pub fn build(kind: ClauseKind, nv: usize, nc: usize) -> ClausePartition {
        let mut head = Vec::with_capacity(1 + nc);
        let mut body = Vec::with_capacity(1 + nc);
        head.push(ClauseHead {
            next_watcher: [NULL_CLAUSE; 2],
            lit: [NULL_LIT; 2],
        });
        body.push(ClauseBody {
            flag: 0,
            lits: vec![],
            rank: RANK_NULL,
            activity: 0.0,
        });
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        let mut touched = Vec::with_capacity(2 * (nv + 1));
        for _i in 0..2 * (nv + 1) {
            watcher.push(NULL_CLAUSE);
            touched.push(false);
        }
        ClausePartition {
            kind,
            init_size: nc,
            head,
            body,
            touched,
            watcher,
        }
    }
    pub fn id_from(&self, cix: ClauseIndex) -> ClauseId {
        cix | self.kind.tag()
    }
    pub fn index_from(&self, cid: ClauseId) -> ClauseIndex {
        cid & self.kind.mask()
    }
    pub fn count(&self, target: Lit, limit: usize) -> usize {
        let mut cnt = 0;
        for _ in self.iter_watcher(target) {
            cnt += 1;
            if 0 < limit && limit <= cnt {
                return limit;
            }
        }
        cnt
    }
}

impl ClauseBody {
    pub fn get_kind(&self) -> ClauseKind {
        match self.flag & 3 {
            0 => ClauseKind::Removable,
            1 => ClauseKind::Permanent,
            2 => ClauseKind::Binclause,
            _ => panic!("impossible clause kind"),
        }
    }
    pub fn set_flag(&mut self, flag: ClauseFlag, val: bool) -> () {
        self.flag &= !(1 << (flag as u16));
        self.flag |= (val as u16) << (flag as u16);
    }
    pub fn get_flag(&self, flag: ClauseFlag) -> bool {
        self.flag & (1 << flag as u16) != 0
    }
}

impl ClauseFlag {
    fn as_bit(self, val: bool) -> u16 {
        (val as u16) << (self as u16)
    }
}

impl ClauseIdIndexEncoding for usize {
    fn to_id(&self) -> ClauseId {
        *self
    }
    #[inline]
    fn to_index(&self) -> ClauseIndex {
        (*self & CLAUSE_INDEX_MASK) as usize
    }
    #[inline]
    fn to_kind(&self) -> usize {
        *self >> CLAUSE_INDEX_BITS
    }
}

impl PartialEq for ClauseBody {
    fn eq(&self, other: &ClauseBody) -> bool {
        self == other
    }
}

impl Eq for ClauseBody {}

impl PartialOrd for ClauseBody {
    fn partial_cmp(&self, other: &ClauseBody) -> Option<Ordering> {
        if self.rank < other.rank {
            Some(Ordering::Less)
        } else if self.rank > other.rank {
            Some(Ordering::Greater)
        } else if self.activity > other.activity {
            Some(Ordering::Less)
        } else if self.activity < other.activity {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl Ord for ClauseBody {
    fn cmp(&self, other: &ClauseBody) -> Ordering {
        if self.rank < other.rank {
            Ordering::Less
        } else if self.rank > other.rank {
            Ordering::Greater
        } else if self.activity > other.activity {
            Ordering::Less
        } else if self.activity < other.activity {
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
            "C lit:{:?}, watches:{:?}",
            vec2int(&self.lit),
            self.next_watcher,
        )
    }
}

impl fmt::Display for ClauseBody {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{{{:?} {}{}{}{}}}",
            vec2int(&self.lits),
            match self.flag & 3 {
                0 => 'L',
                1 => 'P',
                2 => 'B',
                _ => '?',
            },
            if self.get_flag(ClauseFlag::Dead) {
                ", dead"
            } else {
                ""
            },
            if self.get_flag(ClauseFlag::Locked) {
                ", locked"
            } else {
                ""
            },
            if self.get_flag(ClauseFlag::Learnt) {
                ", learnt"
            } else {
                ""
            },
        )
    }
}

pub fn cid2fmt(cid: ClauseId) -> String {
    match cid >> CLAUSE_INDEX_BITS {
        0 => format!("[learnt:{}]", cid.to_index()),
        _ => format!("[prmnnt:{}]", cid.to_index()),
    }
}

pub struct ClauseIter<'a> {
    head: &'a ClauseHead,
    body: &'a ClauseBody,
    end: usize,
    index: usize,
}

pub fn clause_iter<'a>(ch: &'a ClauseHead, cb: &'a ClauseBody) -> ClauseIter<'a> {
    ClauseIter {
        head: ch,
        body: cb,
        end: cb.lits.len() + 2,
        index: 0,
    }
}

impl<'a> Iterator for ClauseIter<'a> {
    type Item = Lit;
    fn next(&mut self) -> Option<Lit> {
        self.index += 1;
        match self.index {
            1 => Some(self.head.lit[0]),
            2 => Some(self.head.lit[1]),
            n if n <= self.end => Some(self.body.lits[n - 3]),
            _ => None,
        }
    }
}

impl ClauseManagement for Solver {
    #[inline]
    fn bump_cid(&mut self, cid: ClauseId) -> () {
        debug_assert_ne!(cid, 0);
        let a;
        {
            let c = clause_body_mut!(self.cp, cid);
            a = c.activity + self.cla_inc;
            c.activity = a;
        }
        if 1.0e20 < a {
            for c in &mut self.cp[ClauseKind::Removable as usize].body[1..] {
                if c.get_flag(ClauseFlag::Learnt) {
                    c.activity *= 1.0e-20;
                }
            }
            self.cla_inc *= 1.0e-20;
        }
    }
    fn decay_cla_activity(&mut self) -> () {
        self.cla_inc /= self.config.clause_decay_rate;
    }
    // renamed from clause_new
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId> {
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means totology.
        for i in 0..v.len() {
            let li = v[i];
            let sat = self.vars.assigned(li);
            if sat == LTRUE || li.negate() == l_ {
                return Some(NULL_CLAUSE);
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
            0 => None, // Empty clause is UNSAT.
            1 => {
                self.enqueue(v[0], NULL_CLAUSE);
                Some(NULL_CLAUSE)
            }
            _ => {
                let cid = self.cp[kind as usize].new_clause(&v, 0, false, false);
                if cid.to_kind() == ClauseKind::Binclause as usize {
                    self.eliminator.binclause_queue.push(cid);
                }
                self.eliminator_enqueue(cid);
                Some(cid)
            }
        }
    }
    /// renamed from newLearntClause
    fn add_clause(&mut self, v: &mut Vec<Lit>, lbd: usize) -> ClauseId {
        debug_assert_ne!(v.len(), 0);
        if v.len() == 1 {
            self.uncheck_enqueue(v[0], NULL_CLAUSE);
            return 0;
        }
        // let lbd = v.lbd(&self.vars, &mut self.lbd_seen);
        let mut i_max = 0;
        let mut lv_max = 0;
        // seek a literal with max level
        for (i, l) in v.iter().enumerate() {
            let vi = l.vi();
            let lv = self.vars[vi].level;
            if self.vars[vi].assign != BOTTOM && lv_max < lv {
                i_max = i;
                lv_max = lv;
            }
        }
        v.swap(1, i_max);
        let kind = if v.len() == 2 {
            ClauseKind::Binclause
        } else if self.strategy == Some(SearchStrategy::ChanSeok) && lbd <= CO_LBD_BOUND {
            ClauseKind::Permanent
        } else if lbd == 0 {
            ClauseKind::Permanent
        } else {
            ClauseKind::Removable
        };
        let cid = self.cp[kind as usize].new_clause(&v, lbd, true, true);
        if kind == ClauseKind::Binclause {
            self.eliminator.binclause_queue.push(cid);
        }
        self.bump_cid(cid);
        self.eliminator_enqueue(cid);
        cid
    }

    fn reduce(&mut self) -> () {
        // self.cp[ClauseKind::Removable as usize].reset_lbd(&self.vars);
        {
            let ClausePartition {
                ref mut head,
                ref mut body,
                ref mut touched,
                ..
            } = &mut self.cp[ClauseKind::Removable as usize];
            let permutation = &mut (1..body.len())
                .filter(|i| !body[*i].get_flag(ClauseFlag::Dead)
                        && !body[*i].get_flag(ClauseFlag::Locked)
                ) // garbage and recycled
                .collect::<Vec<ClauseIndex>>();
            debug_assert!(!permutation.is_empty());
            permutation[1..].sort_by(|&a, &b| body[a].cmp(&body[b]));
            let nc = permutation.len();
            let keep = nc / 2;
            if body[permutation[keep]].rank <= 5 {
                self.next_reduction += 1000;
            };
            for i in keep..nc {
                let ch = &mut head[permutation[i]];
                let mut cb = &mut body[permutation[i]];
                if cb.get_flag(ClauseFlag::JustUsed) {
                    cb.set_flag(ClauseFlag::JustUsed, false)
                } else {
                    cb.set_flag(ClauseFlag::Dead, true);
                    touched[ch.lit[0].negate() as usize] = true;
                    touched[ch.lit[1].negate() as usize] = true;
                }
            }
        }
        // self.garbage_collect(ClauseKind::Removable);
        self.cp[ClauseKind::Removable as usize].garbage_collect();
        // self.cp[ClauseKind::Removable as usize].reset_lbd(&self.vars);
        self.next_reduction += DB_INC_SIZE;
        self.stat[Stat::Reduction as usize] += 1;
    }

    fn simplify(&mut self) -> bool {
        self.eliminate_binclauses();
        debug_assert_eq!(self.decision_level(), 0);
        if self.eliminator.use_elim
            // && self.stat[Stat::Simplification as usize] % 8 == 0
            // && self.eliminator.last_invocatiton < self.stat[Stat::Reduction as usize] as usize
        {
            self.eliminate();
            self.eliminator.last_invocatiton = self.stat[Stat::Reduction as usize] as usize;
        }
        // reset reason since decision level is zero.
        for v in &mut self.vars[1..] {
            if v.reason != NULL_CLAUSE {
                clause_body_mut!(self.cp, v.reason).set_flag(ClauseFlag::Locked, false);
                v.reason = NULL_CLAUSE;
            }
        }
        for ck in &CLAUSE_KINDS {
            for ci in 1..self.cp[*ck as usize].head.len() {
                let ch = &self.cp[*ck as usize].head[ci];
                let cb = &mut self.cp[*ck as usize].body[ci];
                if !cb.get_flag(ClauseFlag::Dead)
                    && (self.vars.satisfies(&ch.lit) || self.vars.satisfies(&cb.lits))
                {
                    cb.set_flag(ClauseFlag::Dead, true);
                    self.cp[*ck as usize].touched[ch.lit[0].negate() as usize] = true;
                    self.cp[*ck as usize].touched[ch.lit[1].negate() as usize] = true;
                }
            }
            self.cp[*ck as usize].garbage_collect();
        }
        self.stat[Stat::Simplification as usize] += 1;
        self.subsume_queue.clear();
        true
    }
    fn lbd_of_an_learnt_lits(&mut self) -> usize {
        let key;
        let key_old = self.lbd_seen[0];
        if 100_000_000 < key_old {
            key = 1;
        } else {
            key = key_old + 1;
        }
        let mut cnt = 0;
        for l in &self.an_learnt_lits {
            let lv = self.vars[l.vi()].level;
            if self.lbd_seen[lv] != key && lv != 0 {
                self.lbd_seen[lv] = key;
                cnt += 1;
            }
        }
        self.lbd_seen[0] = key;
        cnt
    }
    fn lbd_of(&mut self, cid: ClauseId) -> usize {
        let ch = clause_head!(self.cp, cid);
        let cb = clause_body!(self.cp, cid);
        let key;
        let key_old = self.lbd_seen[0];
        if 100_000_000 < key_old {
            key = 1;
        } else {
            key = key_old + 1;
        }
        let mut cnt = 0;
        for l in &ch.lit {
            let lv = self.vars[l.vi()].level;
            if self.lbd_seen[lv] != key && lv != 0 {
                self.lbd_seen[lv] = key;
                cnt += 1;
            }
        }
        for l in &cb.lits {
            let lv = self.vars[l.vi()].level;
            if self.lbd_seen[lv] != key && lv != 0 {
                self.lbd_seen[lv] = key;
                cnt += 1;
            }
        }
        self.lbd_seen[0] = key;
        cnt
    }
    fn biclause_subsume(&mut self, bi: &ClauseHead) -> () {
        for cp in &mut self.cp[..ClauseKind::Binclause as usize] {
            let mut flag = false;
            'next_clause: for i in 1..cp.head.len() {
                let ch = &cp.head[i];
                let cb = &mut cp.body[i];
                if cb.get_flag(ClauseFlag::Dead) {
                    continue;
                }
                let mut cnt = 0;
                for j in 0..cb.lits.len() + 2 {
                    let l = lindex!(ch, cb, j);
                    if l == bi.lit[0] || l == bi.lit[1] {
                        cnt += 1;
                        if cnt == 2 {
                            cb.set_flag(ClauseFlag::Dead, true);
                            cp.touched[ch.lit[0].negate() as usize] = true;
                            cp.touched[ch.lit[1].negate() as usize] = true;
                            flag = true;
                            continue 'next_clause;
                        }
                    }
                }
            }
            if flag {
                cp.garbage_collect();
            }
        }
    }
    fn num_literals(&self, cid: ClauseId) -> usize {
        clause_body!(self.cp, cid).lits.len() + 2
    }
}

impl GC for ClausePartition {
    fn garbage_collect(&mut self) -> () {
        unsafe {
            let garbages = &mut self.watcher[GARBAGE_LIT.negate() as usize] as *mut ClauseId;
            for l in 2..self.watcher.len() {
                if self.touched[l] {
                    self.touched[l] = false;
                } else {
                    continue;
                }
                let vi = (l as Lit).vi();
                let mut pri = &mut self.watcher[l] as *mut usize;
                let mut ci = self.watcher[l];
                while ci != NULL_CLAUSE {
                    let ch = &mut self.head[ci] as *mut ClauseHead;
                    let cb = &mut self.body[ci] as *mut ClauseBody;
                    if !(*cb).get_flag(ClauseFlag::Dead) {
                        pri = &mut (*ch).next_watcher[((*ch).lit[0].vi() != vi) as usize];
                    } else {
                        debug_assert!(
                            (*ch).lit[0].negate() == l as Lit || (*ch).lit[1].negate() == l as Lit
                        );
                        *pri = self.move_to(
                            &mut *garbages,
                            ci,
                            ((*ch).lit[0].negate() != l as Lit) as usize,
                        );
                    }
                    ci = *pri;
                }
            }
            // recycle garbages
            let recycled = &mut self.watcher[RECYCLE_LIT.negate() as usize] as *mut ClauseId;
            let mut pri = &mut self.watcher[GARBAGE_LIT.negate() as usize] as *mut usize;
            let mut ci = self.watcher[GARBAGE_LIT.negate() as usize];
            while ci != NULL_CLAUSE {
                let ch = &mut self.head[ci];
                let cb = &mut self.body[ci];
                debug_assert!(cb.get_flag(ClauseFlag::Dead));
                if ch.lit[0] == GARBAGE_LIT && ch.lit[1] == GARBAGE_LIT {
                    let next = ch.next_watcher[0];
                    *pri = ch.next_watcher[0];
                    ch.lit[0] = RECYCLE_LIT;
                    ch.lit[1] = RECYCLE_LIT;
                    ch.next_watcher[0] = *recycled;
                    ch.next_watcher[1] = *recycled;
                    *recycled = ci;
                    cb.set_flag(ClauseFlag::Locked, true);
                    ci = next;
                } else {
                    debug_assert!(ch.lit[0] == GARBAGE_LIT || ch.lit[1] == GARBAGE_LIT);
                    let index = (ch.lit[0] != GARBAGE_LIT) as usize;
                    ci = ch.next_watcher[index];
                    pri = &mut ch.next_watcher[index];
                }
            }
        }
        debug_assert_eq!(self.watcher[GARBAGE_LIT.negate() as usize], NULL_CLAUSE);
    }
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool, locked: bool) -> ClauseId {
        let cix;
        let w0;
        let w1;
        if self.watcher[RECYCLE_LIT.negate() as usize] != NULL_CLAUSE {
            cix = self.watcher[RECYCLE_LIT.negate() as usize];
            debug_assert_eq!(self.body[cix].get_flag(ClauseFlag::Dead), true);
            debug_assert_eq!(self.head[cix].lit[0], RECYCLE_LIT);
            debug_assert_eq!(self.head[cix].lit[1], RECYCLE_LIT);
            self.watcher[RECYCLE_LIT.negate() as usize] = self.head[cix].next_watcher[0];
            let ch = &mut self.head[cix];
            let cb = &mut self.body[cix];
            ch.lit[0] = v[0];
            ch.lit[1] = v[1];
            cb.lits.clear();
            for l in &v[2..] {
                cb.lits.push(*l);
            }
            cb.rank = rank;
            cb.flag = self.kind as u16; // reset Dead, JustUsed, SveMark and Touched
            cb.set_flag(ClauseFlag::Locked, locked);
            cb.set_flag(ClauseFlag::Learnt, learnt);
            cb.activity = 0.0;
            w0 = ch.lit[0].negate() as usize;
            w1 = ch.lit[1].negate() as usize;
            ch.next_watcher[0] = self.watcher[w0];
            ch.next_watcher[1] = self.watcher[w1];
        } else {
            let l0 = v[0];
            let l1 = v[1];
            let mut lits = Vec::with_capacity(v.len() - 2);
            for l in &v[2..] {
                lits.push(*l);
            }
            cix = self.head.len();
            w0 = l0.negate() as usize;
            w1 = l1.negate() as usize;
            self.head.push(ClauseHead {
                lit: [l0, l1],
                next_watcher: [self.watcher[w0], self.watcher[w1]],
            });
            self.body.push(ClauseBody {
                flag: self.kind as u16
                    | ClauseFlag::Locked.as_bit(locked)
                    | ClauseFlag::Learnt.as_bit(learnt),
                lits,
                rank,
                activity: 1.0,
            });
        };
        self.watcher[w0] = cix;
        self.watcher[w1] = cix;
        self.id_from(cix)
    }
    fn reset_lbd(&mut self, vars: &[Var]) -> () {
        let mut temp = Vec::with_capacity(vars.len());
        for _ in 0..vars.len() {
            temp.push(0);
        }
        for i in 1..self.head.len() {
            let ch = &mut self.head[i];
            let cb = &mut self.body[i];
            if cb.get_flag(ClauseFlag::Dead) {
                continue;
            }
            let key = i;
            let mut cnt = 0;
            for l in &ch.lit {
                let lv = vars[l.vi()].level;
                if temp[lv] != key && lv != 0 {
                    temp[lv] = key;
                    cnt += 1;
                }
            }
            for l in &cb.lits {
                let lv = vars[l.vi()].level;
                if temp[lv] != key && lv != 0 {
                    temp[lv] = key;
                    cnt += 1;
                }
            }
            cb.rank = cnt;
        }
    }
    fn move_to(&mut self, list: &mut ClauseId, ci: ClauseIndex, index: usize) -> ClauseIndex {
        debug_assert!(index == 0 || index == 1);
        let other = (index ^ 1) as usize;
        debug_assert!(other == 0 || other == 1);
        let ch = &mut self.head[ci];
        ch.lit[index] = GARBAGE_LIT;
        let next = ch.next_watcher[index];
        if ch.lit[other] == GARBAGE_LIT {
            ch.next_watcher[index] = ch.next_watcher[other];
        } else {
            ch.next_watcher[index] = *list;
            *list = ci;
        }
        next
    }
}

pub struct ClauseListIter<'a> {
    vec: &'a Vec<ClauseHead>,
    target: Lit,
    next_index: ClauseIndex,
}

impl<'a> ClausePartition {
    pub fn iter_watcher(&'a self, p: Lit) -> ClauseListIter<'a> {
        ClauseListIter {
            vec: &self.head,
            target: p,
            next_index: self.watcher[p.negate() as usize],
        }
    }
}

impl<'a> Iterator for ClauseListIter<'a> {
    type Item = ClauseIndex;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next_index == NULL_CLAUSE {
            None
        } else {
            let i = self.next_index as usize;
            let c = &self.vec[self.next_index as usize];
            self.next_index = c.next_watcher[(c.lit[0] != self.target) as usize];
            Some(i)
        }
    }
}

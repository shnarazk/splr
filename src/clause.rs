use std::cmp::Ordering;
use std::f64;
use std::fmt;
use std::usize::MAX;
use types::*;
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use var::Satisfiability;

/// for ClauseIndex
pub trait ClauseList {
    fn push(&mut self, cix: ClauseIndex, list: &mut ClauseIndex) -> ClauseIndex;
    fn push_garbage(&mut self, c: &mut Clause, index: usize) -> ClauseIndex;
}

/// for usize, Clause
pub trait ClauseIdIndexEncoding {
    fn to_id(&self) -> ClauseId;
    fn to_index(&self) -> ClauseIndex;
    fn to_kind(&self) -> usize;
}

pub trait ClauseManagement {
    fn bump_cid(&mut self, ci: ClauseId) -> ();
    fn decay_cla_activity(&mut self) -> ();
    fn add_clause(&mut self, v: &mut Vec<Lit>) -> bool;
    fn add_learnt(&mut self, v: &mut Vec<Lit>) -> usize;
    fn reduce_watchers(&mut self) -> ();
    fn simplify_database(&mut self) -> bool;
    fn lbd_of(&mut self, v: &[Lit]) -> usize;
}

// const DB_INIT_SIZE: usize = 1000;
const DB_INC_SIZE: usize = 50;
pub const KINDS: [ClauseKind; 3] = [
    ClauseKind::Binclause,
    ClauseKind::Permanent,
    ClauseKind::Removable,
];

#[derive(Debug)]
pub struct ClausePack {
    pub kind: ClauseKind,
    pub init_size: usize,
    pub clauses: Vec<Clause>,
    pub touched: Vec<bool>,
    pub permutation: Vec<ClauseIndex>,
    pub watcher: Vec<ClauseIndex>,
    pub tag: usize,
    pub mask: usize,
    pub index_bits: usize,
}

#[derive(Clone, Copy, Debug)]
pub enum ClauseKind {
    Removable = 0,
    Permanent,
    Binclause,
}

pub const CLAUSE_KINDS: [ClauseKind; 3] = [
    ClauseKind::Removable,
    ClauseKind::Permanent,
    ClauseKind::Binclause,
];

const CLAUSE_INDEX_BITS: usize = 60;
const CLAUSE_INDEX_MASK: usize = 0x0FFF_FFFF_FFFF_FFFF;
pub const DEAD_CLAUSE: usize = MAX;

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

impl ClausePack {
    pub fn build(kind: ClauseKind, nv: usize, nc: usize) -> ClausePack {
        let tag = kind.tag();
        let mask = kind.mask();
        let mut clauses = Vec::with_capacity(1 + nc);
        clauses.push(Clause::null());
        let mut permutation = Vec::new();
        permutation.push(0); // for NULL_CLAUSE
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        let mut touched = Vec::with_capacity(2 * (nv + 1));
        for _i in 0..2 * (nv + 1) {
            watcher.push(NULL_CLAUSE);
            touched.push(false);
        }

        ClausePack {
            kind,
            init_size: nc,
            clauses,
            touched,
            permutation,
            watcher,
            mask,
            tag,
            index_bits: CLAUSE_INDEX_BITS,
        }
    }
    pub fn attach(&mut self, mut c: Clause) -> ClauseId {
        let w0 = c.lit[0].negate() as usize;
        let w1 = c.lit[1].negate() as usize;
        let cix = self.clauses.len();
        c.index = cix;
        self.permutation.push(cix);
        c.next_watcher[0] = self.watcher[w0];
        self.watcher[w0] = cix;
        c.next_watcher[1] = self.watcher[w1];
        self.watcher[w1] = cix;
        self.clauses.push(c);
        self.id_from(cix)
    }
    pub fn id_from(&self, cix: ClauseIndex) -> ClauseId {
        cix | self.tag
    }
    pub fn index_from(&self, cid: ClauseId) -> ClauseIndex {
        cid & self.mask
    }
    pub fn len(&self) -> usize {
        self.clauses.len()
    }
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }
}

impl Clause {
    pub fn set_flag(&mut self, flag: ClauseFlag, val: bool) -> () {
        self.flags &= !(1 << (flag as u32));
        self.flags |= (val as u32) << (flag as u32);

    }
    pub fn get_flag(&self, flag: ClauseFlag) -> bool {
        self.flags & (1 << flag as u32) != 0
    }
}

pub const RANK_NULL: usize = 0; // for NULL_CLAUSE
pub const RANK_CONST: usize = 1; // for given clauses
pub const RANK_NEED: usize = 2; // for newly generated bi-clauses

/// Clause Index, not ID because it's used only within a Vec<Clause>
pub type ClauseIndex = usize;

/// Clause
#[derive(Debug)]
pub struct Clause {
    /// kind has 3 types.
    pub kind: ClauseKind,
    /// a temporal index which is equal to the index for `clauses` or `learnts`
    pub index: ClauseId,
    /// clause activity used by `analyze` and `reduce_db`
    pub activity: f64,
    /// LBD or NDD and so on, used by `reduce_db`
    pub rank: usize,
    /// ClauseIndexes of the next in the watch liss
    pub next_watcher: [ClauseIndex; 2],
    /// The first two literals
    pub lit: [Lit; 2],
    /// the literals without lit0 and lit1
    pub lits: Vec<Lit>,
    pub flags: u32
//    /// used for a reason of propagation
//    pub locked: bool,
//    /// given or learnt
//    pub learnt: bool,
//    /// for elimination-by-simplfication
//    pub frozen: bool,
//    /// used in the current phase
//    pub just_used: bool,
//    /// used in Subsumption Variable Eliminator
//    pub sve_mark: bool,
//    /// used in Subsumption Variable Eliminator
//    pub touched: bool,
//    /// gc
//    pub dead: bool,
}

#[derive(Copy, Clone)]
pub enum ClauseFlag {
    Dead = 0,
    Locked,
    Learnt,
    JustUsed,
    SveMark,
    Touched,
    Frozen,
}

impl ClauseFlag {
    fn as_bit(self, val: bool) -> u32 {
        (val as u32) << (self as u32)
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

impl ClauseIdIndexEncoding for Clause {
    fn to_id(&self) -> ClauseId {
        self.index | self.kind.tag()
    }
    fn to_index(&self) -> ClauseIndex {
        self.index
    }
    fn to_kind(&self) -> usize {
        self.kind as usize
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Clause) -> bool {
        self.index == other.index
    }
}

impl Eq for Clause {}

impl PartialOrd for Clause {
    /// the key is `tmp`, not `rank`, since we want to reflect whether it's used as a reason.
    fn partial_cmp(&self, other: &Clause) -> Option<Ordering> {
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

impl Ord for Clause {
    fn cmp(&self, other: &Clause) -> Ordering {
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

impl Clause {
    pub fn new(kind: ClauseKind, learnt: bool, rank: usize, v: &[Lit]) -> Clause {
        let mut v = v.to_owned();
        let lit0 = v.remove(0);
        let lit1 = v.remove(0);
        Clause {
            kind,
//            learnt,
            activity: 0.0,
            rank,
            next_watcher: [NULL_CLAUSE; 2],
            lit: [lit0, lit1],
            lits: v,
            index: 0,
            flags: ClauseFlag::Learnt.as_bit(learnt),
//            locked: false,
//            frozen: false,
//            just_used: false,
//            sve_mark: false,
//            touched: false,
//            dead: false,
        }
    }
    pub fn null() -> Clause {
        Clause {
            kind: ClauseKind::Permanent,
            activity: 0.0,
            rank: RANK_NULL,
            next_watcher: [NULL_CLAUSE; 2],
            lit: [NULL_LIT; 2],
            lits: vec![],
            index: 0,
            flags: 0,
        }
    }
    pub fn len(&self) -> usize {
        self.lits.len() + 2
    }
    pub fn is_empty(&self) -> bool {
        false
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if f.alternate() {
            write!(
                f,
                "C{} rank:{}, activity: {}, lit:{:?}{:?}",
                self.index, self.rank, self.activity, self.lit, self.lits,
            )
        } else {
            match self.index {
                //            x if x < 0 => write!(f, format!("a given clause {}", self.lits.map(|l| l.int()))),
                0 => write!(f, "null_clause"),
                DEAD_CLAUSE => write!(
                    f,
                    "dead[{},{}]{:?}",
                    self.lit[0].int(),
                    self.lit[1].int(),
                    &self.lits.iter().map(|l| l.int()).collect::<Vec<i32>>()
                ),
                _ if self.lits.is_empty() => write!(
                    f,
                    "B{}[{},{}]",
                    self.index,
                    self.lit[0].int(),
                    self.lit[1].int(),
                ),
                _ => write!(
                    f,
                    "{}{}[{},{}]{:?}",
                    match self.kind {
                        ClauseKind::Removable => 'L',
                        ClauseKind::Binclause => 'B',
                        ClauseKind::Permanent => 'P',
                    },
                    self.index,
                    self.lit[0].int(),
                    self.lit[1].int(),
                    &self.lits.iter().map(|l| l.int()).collect::<Vec<i32>>(),
                ),
            }
        }
    }
}

pub fn cid2fmt(cid: ClauseId) -> String {
    match cid >> CLAUSE_INDEX_BITS {
        0 => format!("[learnt:{}]", cid.to_index()),
        _ => format!("[prmnnt:{}]", cid.to_index()),
    }
}

impl Dump for [ClausePack] {
    fn dump(&self, str: &str) -> () {
        println!("dumped {}", str);
    }
}

impl Clause {
    pub fn subsumes(&self, other: &Clause) -> Option<Lit> {
        let mut ret: Lit = NULL_LIT;
        'next: for i in 0..self.len() {
            let l = lindex!(self, i);
            for j in 0..other.len() {
                let lo = lindex!(other, j);
                if l == lo {
                    continue 'next;
                } else if ret == NULL_LIT && l == lo.negate() {
                    ret = l;
                    continue 'next;
                }
            }
            return None;
        }
        Some(ret)
    }
    /// remove Lit `p` from Clause *self*.
    /// returns true if the clause became a unit clause.
    pub fn strengthen(&mut self, p: Lit) -> bool {
        if self.get_flag(ClauseFlag::Frozen) {
            return false;
        }
        let len = self.len();
        if len == 2 {
            if self.lit[0] == p {
                self.lit.swap(0, 1);
            }
            return true;
        }
        if self.lit[0] == p {
            self.lit[0] = self.lits.pop().unwrap();
        } else if self.lit[1] == p {
            self.lit[1] = self.lits.pop().unwrap();
        } else {
            self.lits.retain(|&x| x != p);
        }
        false
    }
}

pub struct ClauseIter<'a> {
    clause: &'a Clause,
    end: usize,
    index: usize,
}

impl<'a> IntoIterator for &'a Clause {
    type Item = Lit;
    type IntoIter = ClauseIter<'a>;
    fn into_iter(self) -> ClauseIter<'a> {
        ClauseIter {
            clause: &self,
            end: self.len(),
            index: 0,
        }
    }
}

impl<'a> Iterator for ClauseIter<'a> {
    type Item = Lit;
    fn next(&mut self) -> Option<Lit> {
        self.index += 1;
        match self.index {
            1 => Some(self.clause.lit[0]),
            2 => Some(self.clause.lit[1]),
            n if n <= self.end => Some(self.clause.lits[n - 3]),
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
            // let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            let c = mref!(self.cp, cid);
            a = c.activity + self.cla_inc;
            c.activity = a;
        }
        if 1.0e20 < a {
            for c in &mut self.cp[ClauseKind::Removable as usize].clauses {
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
    fn add_clause(&mut self, v: &mut Vec<Lit>) -> bool {
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means totology.
        for i in 0..v.len() {
            let li = v[i];
            let sat = self.vars.assigned(li);
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
            0 => false, // Empty clause is UNSAT.
            1 => self.enqueue(v[0], NULL_CLAUSE),
            _ => {
                self.cp[kind as usize].new_clause(&v, 0, false, false);
                true
            }
        }
    }
    /// renamed from newLearntClause
    fn add_learnt(&mut self, v: &mut Vec<Lit>) -> usize {
        debug_assert_ne!(v.len(), 0);
        if v.len() == 1 {
            self.uncheck_enqueue(v[0], NULL_CLAUSE);
            return 0;
        }
        let lbd = self.lbd_of(&v);
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
        let l0 = v[0];
        let kind = if v.len() == 2 {
            ClauseKind::Binclause
        } else {
            ClauseKind::Removable
        };
        let cid = self.cp[kind as usize].new_clause(&v, lbd, true, true);
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
                ref mut touched,
                ..
            } = &mut self.cp[ClauseKind::Removable as usize];
            let permutation = &mut (1..clauses.len())
                .filter(|i| !clauses[*i].get_flag(ClauseFlag::Dead)) // garbage and recycled
                .collect::<Vec<ClauseIndex>>();

            // debug_assert_eq!(permutation.len(), clauses.len());
            // sort the range of 'permutation'
            permutation[1..].sort_by(|&a, &b| clauses[a].cmp(&clauses[b]));
            let nc = permutation.len();
            for i in nc / 2 + 1..nc {
                let mut c = &mut clauses[permutation[i]];
                if !c.get_flag(ClauseFlag::Locked) && !c.get_flag(ClauseFlag::JustUsed) {
                    c.set_flag(ClauseFlag::Dead, true);
                    touched[c.lit[0].negate() as usize] = true;
                    touched[c.lit[1].negate() as usize] = true; 
                }
            }
        }
        // self.garbage_collect(ClauseKind::Removable);
        self.cp[ClauseKind::Removable as usize].garbage_collect();
        self.next_reduction += DB_INC_SIZE + (self.c_lvl.0 as usize);
        self.stats[Stat::NumOfReduction as usize] += 1;
        self.progress("drop");
    }
    fn simplify_database(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        if self.eliminator.use_elim
            && self.stats[Stat::NumOfSimplification as usize] % 8 == 0
            && self.eliminator.last_invocatiton < self.stats[Stat::NumOfReduction as usize] as usize
        {
            // self.eliminate();
            self.eliminator.last_invocatiton = self.stats[Stat::NumOfReduction as usize] as usize;
        }
        // remove unsatisfiable literals in clauses
        let targets: Vec<Lit> = self.trail[self.num_solved_vars..]
            .iter()
            .map(|l| l.negate())
            .collect();
        for ck in &KINDS {
            debug_assert_eq!(self.cp[*ck as usize].clauses[0].index, 0);
            for mut c in &mut self.cp[*ck as usize].clauses {
                if !(*c).get_flag(ClauseFlag::Frozen) {
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
                    if ((*c).get_flag(ClauseFlag::Frozen) && thr < (*c).len()) || self.vars.satisfies(&*c) {
                        // (*c).index = DEAD_CLAUSE;
                        (*c).set_flag(ClauseFlag::Dead, true);
                        self.cp[*ck as usize].touched[(*c).lit[0].negate() as usize] = true;
                        self.cp[*ck as usize].touched[(*c).lit[1].negate() as usize] = true; 
                    } else if (*c).lits.is_empty() && false {
                        if !self.enqueue((*c).lits[0], NULL_CLAUSE) {
                            self.ok = false;
                        }
                        (*c).set_flag(ClauseFlag::Dead, true);
                        self.cp[*ck as usize].touched[(*c).lit[0].negate() as usize] = true;
                        self.cp[*ck as usize].touched[(*c).lit[1].negate() as usize] = true; 
                        // (*c).index = DEAD_CLAUSE;
                        // } else {
                        //     let new = self.lbd_of(&(*c).lits);
                        //     if new < (*c).rank {
                        //         (*c).rank = new;
                        //     }
                        // }
                    }
                    (*c).set_flag(ClauseFlag::Frozen, false);
                }
            }
            self.cp[*ck as usize].garbage_collect();
            // self.garbage_collect(*ck);
        }
        self.stats[Stat::NumOfSimplification as usize] += 1;
//        if self.eliminator.use_elim
//            && self.stats[Stat::NumOfSimplification as usize] % 8 == 0
//            && self.eliminator.last_invocatiton < self.stats[Stat::NumOfReduction as usize] as usize
//        {
//            self.eliminate();
//            self.eliminator.last_invocatiton = self.stats[Stat::NumOfReduction as usize] as usize;
//            for ck in &KINDS {
//                // self.garbage_collect(*ck);
//                self.cp[*ck as usize].garbage_collect();
//            }
//        }
        self.progress("simp");
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
    pub fn garbage_collect_compaction(&mut self, kind: ClauseKind) -> () {
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
                if !c.get_flag(ClauseFlag::Dead) {
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
            clauses.retain(|ref c| !c.get_flag(ClauseFlag::Dead));
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
            if c.get_flag(ClauseFlag::Frozen) || c.index == DEAD_CLAUSE {
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
        let k = if self.trail_lim.is_empty() {
            self.trail.len()
        } else {
            self.trail_lim[0]
        };
        let sum = k + self.eliminator.eliminated_vars;
        println!(
            "#{}, DB:R|P|B, {:>8}, {:>8}, {:>5}, Progress: {:>6}+{:>6}({:>4.1}%), Restart:b|f, {:>6}, {:>6}, EMA:a|l, {:>5.2}, {:>6.2}, LBD: {:>5.2}",
            mes,
            self.cp[ClauseKind::Removable as usize].clauses.len() - 1,
            self.cp[ClauseKind::Permanent as usize].clauses.len() - 1,
            self.cp[ClauseKind::Binclause as usize].clauses.len() - 1,
            k,
            self.eliminator.eliminated_vars,
            (sum as f32) / (nv as f32),
            self.stats[Stat::NumOfBlockRestart as usize],
            self.stats[Stat::NumOfRestart as usize],
            self.ema_asg.get(),
            self.ema_lbd.get(),
            self.ema_lbd.fast,
        );
    }
}

trait GC {
    fn garbage_collect(&mut self) ->  ();
    fn new_clause(&mut self, v: &Vec<Lit>, rank: usize, learnt: bool, locked: bool) -> ClauseId;
}

impl GC for ClausePack {
    fn garbage_collect(&mut self) -> () {
        // let mut ci = self.watcher[GARBAGE_LIT.negate() as usize];
        // while ci != NULL_CLAUSE {
        //     let c = &self.clauses[ci];
        //     debug_assert!(c.dead);
        //     debug_assert!(c.lit[0] == GARBAGE_LIT || c.lit[1] == GARBAGE_LIT);
        //     let index = (c.lit[0] != GARBAGE_LIT) as usize;
        //     ci = c.next_watcher[index];
        // }
        unsafe {
            let garbages = &mut self.watcher[GARBAGE_LIT.negate() as usize] as *mut ClauseId;
            for l in 2..self.watcher.len() {
                if self.touched[l] {
                    self.touched[l] = false;
                } else {
                    continue;
                }
                let vi = (l as Lit).vi();
                let mut pri = &mut self.watcher[l] as *mut ClauseId;
                let mut ci = self.watcher[l];
                while ci != NULL_CLAUSE {
                    let c = &mut self.clauses[ci] as *mut Clause;
                    if !(*c).get_flag(ClauseFlag::Dead) {
                        if (*c).lit[0].vi() == vi {
                            pri = &mut (*c).next_watcher[0];
                            ci = *pri;
                        } else {
                            pri = &mut (*c).next_watcher[1];
                            ci = *pri;
                        }
                        continue;
                    }
                    // debug_assert!((*c).lit[0] == GARBAGE_LIT || (*c).lit[1] == GARBAGE_LIT);
                    if (*c).lit[0].negate() == l as Lit {
                        *pri = (*garbages).push_garbage(&mut *c, 0);
                        ci = *pri;
                    } else if (*c).lit[1].negate() == l as Lit {
                        *pri = (*garbages).push_garbage(&mut *c, 1);
                        ci = *pri;
                    } else {
                        panic!("xxxxx {:?}", (*c).lit);
                    }
                }
            }
            // recycle garbages
            let recycled = &mut self.watcher[RECYCLE_LIT.negate() as usize] as *mut ClauseId;
            let mut pri = &mut self.watcher[GARBAGE_LIT.negate() as usize] as *mut ClauseId;
            let mut ci = self.watcher[GARBAGE_LIT.negate() as usize];
            while ci != NULL_CLAUSE {
                let c = &mut self.clauses[ci];
                debug_assert!(c.get_flag(ClauseFlag::Dead));
                if c.lit[0] == GARBAGE_LIT && c.lit[1] == GARBAGE_LIT {
                    let next = c.next_watcher[0];
                    *pri = c.next_watcher[0];
                    c.lit[0] = RECYCLE_LIT;
                    c.lit[1] = RECYCLE_LIT;
                    c.next_watcher[0] = *recycled;
                    c.next_watcher[1] = *recycled;
                    *recycled = ci;
                    c.set_flag(ClauseFlag::Locked, true);
                    ci = next;
                } else {
                    debug_assert!(c.lit[0] == GARBAGE_LIT || c.lit[1] == GARBAGE_LIT);
                    let index = (c.lit[0] != GARBAGE_LIT) as usize;
                    ci = c.next_watcher[index];
                    pri = &mut c.next_watcher[index];
                }
            }
        }
        debug_assert_eq!(self.watcher[0], NULL_CLAUSE);
        // // ASSERTION
        // {
        //     for i in 2..self.watcher.len() {
        //         let mut ci = self.watcher[i];
        //         while ci != NULL_CLAUSE {
        //             if self.clauses[ci].dead {
        //                 panic!("aeaaeamr");
        //             }
        //             let index = self.clauses[ci].lit[0].negate() != i as Lit;
        //             ci = self.clauses[ci].next_watcher[index as usize];
        //         }
        //     }
        // }
    }
    fn new_clause(&mut self, v: &Vec<Lit>, rank: usize, learnt: bool, locked: bool) -> ClauseId {
        let cix;
        let w0;
        let w1;
        if self.watcher[RECYCLE_LIT.negate() as usize] != NULL_CLAUSE {
            cix = self.watcher[RECYCLE_LIT.negate() as usize];
            debug_assert_eq!(self.clauses[cix].get_flag(ClauseFlag::Dead), true);
            debug_assert_eq!(self.clauses[cix].lit[0], RECYCLE_LIT);
            debug_assert_eq!(self.clauses[cix].lit[1], RECYCLE_LIT);
            debug_assert_eq!(self.clauses[cix].index, cix);
            self.watcher[RECYCLE_LIT.negate() as usize] = self.clauses[cix].next_watcher[0];
            let c = &mut self.clauses[cix];
            c.lit[0] = v[0];
            c.lit[1] = v[1];
            c.lits.clear();
            for l in &v[2..] {
                c.lits.push(*l);
            }
            c.rank = rank;
            c.set_flag(ClauseFlag::Locked, locked);
            c.set_flag(ClauseFlag::Learnt, learnt);
            c.set_flag(ClauseFlag::Dead, false);
            c.set_flag(ClauseFlag::JustUsed, false);
            c.set_flag(ClauseFlag::SveMark, false);
            c.set_flag(ClauseFlag::Touched, false);
            c.activity = 0.0;
            w0 = c.lit[0].negate() as usize;
            w1 = c.lit[1].negate() as usize;
            c.next_watcher[0] = self.watcher[w0];
            c.next_watcher[1] = self.watcher[w1];
        } else {
            cix = self.clauses.len();
            // make a new clause as c
            let mut c = Clause::new(self.kind, learnt, rank, &v);
            c.index = cix;
            w0 = c.lit[0].negate() as usize;
            w1 = c.lit[1].negate() as usize;
            debug_assert_ne!(w0, 0);
            debug_assert_ne!(w1, 0);
            // self.permutation.push(cix);
            c.next_watcher[0] = self.watcher[w0];
            c.next_watcher[1] = self.watcher[w1];
            self.clauses.push(c);
        };
        self.watcher[w0] = cix;
        self.watcher[w1] = cix;
        self.id_from(cix)
    }
}

impl ClauseList for ClauseIndex {
    fn push(&mut self, cix: ClauseIndex, item: &mut ClauseIndex) -> ClauseIndex {
        *item = *self;
        *self = cix;
        *item
    }
    fn push_garbage(&mut self, c: &mut Clause, index: usize) -> ClauseIndex {
        debug_assert!(index == 0 || index == 1);
        let other = (index ^ 1) as usize;
        debug_assert!(other == 0 || other == 1);
        c.lit[index] = GARBAGE_LIT;
        let next = c.next_watcher[index];
        if c.lit[other] == GARBAGE_LIT {
            c.next_watcher[index] = c.next_watcher[other];
        } else {
            self.push(c.index, &mut c.next_watcher[index]);
            // println!(" push_garbage {:#} <= {}", c, *self);
        }
        next
    }
}

use assign::{AssignState, Assignment};
use std::cmp::Ordering;
use std::f64;
use std::fmt;
use std::usize::MAX;
use types::LiteralEncoding;
use types::*;
use var::Satisfiability;
use var::Var;

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

/// for ClausePack
pub trait ClauseIF {
    fn propagate(
        &mut self,
        assign: &mut [Lbool],
        vars: &mut [Var],
        asg: &mut AssignState,
        p: Lit,
    ) -> ClauseId;
    fn garbage_collect(&mut self) -> ();
    fn id_from(&self, cix: ClauseIndex) -> ClauseId;
    fn index_from(&self, cid: ClauseId) -> ClauseIndex;
    fn new_clause(&mut self, v: &Vec<Lit>, rank: usize, learnt: bool, locked: bool) -> ClauseId;
    fn len(&self) -> usize;
    fn count(&self, target: Lit, limit: usize) -> usize;
}

/// for ClauseDBState
pub trait ClauseManagement {
    fn bump(&mut self, cp: &mut [ClausePack; 3], ci: ClauseId) -> ();
    fn decay_cla_activity(&mut self) -> ();
    fn reduce(&mut self, cp: &mut ClausePack, thr: f64) -> ();
    fn simplify(&mut self, cp: &mut [ClausePack; 3], assign: &Vec<Lbool>) -> bool;
}

const DEBUG: usize = 27728;
const WATCHING: VarId = 2685;
const CLAUSE_INDEX_BITS: usize = 60;
const CLAUSE_INDEX_MASK: usize = 0x0FFF_FFFF_FFFF_FFFF;

// const DB_INIT_SIZE: usize = 1000;
pub const KINDS: [ClauseKind; 3] = [
    ClauseKind::Removable,
    ClauseKind::Permanent,
    ClauseKind::Binclause,
];
pub const DEAD_CLAUSE: usize = MAX;

pub const CLAUSE_KINDS: [ClauseKind; 3] = [
    ClauseKind::Removable,
    ClauseKind::Permanent,
    ClauseKind::Binclause,
];

/// Clause Index, not ID because it's used only within a Vec<Clause>
pub type ClauseIndex = usize;

/// Clause
#[derive(Debug)]
pub struct Clause {
    /// kind has 3 types.
    pub kind: ClauseKind,
    /// a temporal index which is equal to the index for `clauses` or `learnts`
    pub index: ClauseId,
    /// LBD or NDD and so on, used by `reduce_db`
    pub rank: usize,
    /// ClauseIndexes of the next in the watch liss
    pub next_watcher: [ClauseIndex; 2],
    /// The first two literals
    pub lit: [Lit; 2],
    /// the literals without lit0 and lit1
    pub lits: Vec<Lit>,
    pub dead: bool,
    /// used for a reason of propagation
    pub locked: bool,
    /// given or learnt
    pub learnt: bool,
    /// used in the current phase
    pub just_used: bool,
    /// used in Subsumption Variable Eliminator
    pub sve_mark: bool,
    /// used in Subsumption Variable Eliminator
    pub touched: bool,
    /// clause activity used by `analyze` and `reduce_db`
    pub activity: f64,
}

#[derive(Debug)]
pub struct ClausePack {
    pub kind: ClauseKind,
    pub init_size: usize,
    pub clauses: Vec<Clause>,
    // pub permutation: Vec<ClauseIndex>,
    pub watcher: Vec<ClauseIndex>,
    pub tag: usize,
    pub mask: usize,
    pub index_bits: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClauseKind {
    Removable = 0,
    Permanent,
    Binclause,
}

#[derive(Debug)]
pub struct ClauseDBState {
    pub cla_inc: f64,
    pub decay_rate: f64,
    pub increment_step: usize,
}

impl ClauseKind {
    pub fn tag(&self) -> usize {
        match self {
            ClauseKind::Removable => 0x0000_0000_0000_0000,
            ClauseKind::Permanent => 0x1000_0000_0000_0000,
            ClauseKind::Binclause => 0x2000_0000_0000_0000,
        }
    }
    pub fn mask(&self) -> usize {
        CLAUSE_INDEX_MASK
    }
    pub fn id_from(&self, cix: ClauseIndex) -> ClauseId {
        cix | self.tag()
    }
    pub fn index_from(&self, cid: ClauseId) -> ClauseIndex {
        cid & self.mask()
    }
}

impl ClauseIF for ClausePack {
    fn propagate(
        &mut self,
        assign: &mut [Lbool],
        vars: &mut [Var],
        asg: &mut AssignState,
        p: Lit,
    ) -> ClauseId {
        let ClausePack {
            ref mut clauses,
            ref mut watcher,
            kind,
            ..
        } = self;
        let false_lit = (p as Lit).negate();
        debug_assert_eq!(GARBAGE_LIT.negate() as usize, 0);
        let mut ci: ClauseIndex = watcher[p as usize];
        watcher[p as usize] = NULL_CLAUSE;
        let mut tail = &mut watcher[p as usize] as *mut usize;
        {
            'next_clause: while ci != NULL_CLAUSE {
                let c = &mut clauses[ci];
                debug_assert!(!(*c).dead);
                if (*c).lit[0] == false_lit {
                    (*c).lit.swap(0, 1); // now my index is 1, others is 0.
                    (*c).next_watcher.swap(0, 1);
                }
                let next = (*c).next_watcher[1];
                let other = (*c).lit[0];
                let first_value = (&assign[..]).assigned(other);
                if first_value != LTRUE {
                    for k in 0..(*c).lits.len() {
                        let lk = (*c).lits[k];
                        // below is equivalent to 'self.assigned(lk) != LFALSE'
                        if (((lk & 1) as u8) ^ assign[lk.vi()]) != 0 {
                            let lk_watcher = &mut watcher[lk.negate() as usize];
                            (*c).lit[1] = lk;
                            (*c).lits[k] = false_lit;
                            (*c).next_watcher[1] = *lk_watcher;
                            *lk_watcher = ci;
                            ci = next;
                            continue 'next_clause;
                        }
                    }
                    if first_value == LFALSE {
                        unsafe {
                            *tail = ci;
                        }
                        return kind.id_from(ci);
                    } else {
                        asg.uncheck_enqueue(assign, &mut vars[other.vi()], other, kind.id_from(ci));
                        (*c).locked = true;
                    }
                }
                {
                    // reconnect
                    let watch = watcher[p as usize];
                    if watch == NULL_CLAUSE {
                        tail = &mut (*c).next_watcher[1];
                    }
                    (*c).next_watcher[1] = watch;
                    watcher[p as usize] = ci;
                }
                ci = next;
            }
        }
        NULL_CLAUSE
    }
    fn garbage_collect(&mut self) -> () {
        let mut ci = self.watcher[GARBAGE_LIT.negate() as usize];
        while ci != NULL_CLAUSE {
            let c = &self.clauses[ci];
            debug_assert!(c.dead);
            debug_assert!(c.lit[0] == GARBAGE_LIT || c.lit[1] == GARBAGE_LIT);
            let index = (c.lit[0] != GARBAGE_LIT) as usize;
            ci = c.next_watcher[index];
        }
        unsafe {
            for l in 2..self.watcher.len() {
                let vi = (l as Lit).vi();
                let mut garbages =
                    &mut self.watcher[GARBAGE_LIT.negate() as usize] as *mut ClauseId;
                let mut pri = &mut self.watcher[l] as *mut ClauseId;
                let mut ci = self.watcher[l];
                'next_clause: while ci != NULL_CLAUSE {
                    let c = &mut self.clauses[ci] as *mut Clause;
                    // if vi == WATCHING || (*c).index == DEBUG { println!("# garbage collect: traverser finds on {} : {:#}", vi, *c); }
                    if !(*c).dead {
                        debug_assert!(!(*c).dead);
                        if (*c).lit[0].vi() == vi {
                            pri = &mut (*c).next_watcher[0];
                            ci = *pri;
                        } else {
                            pri = &mut (*c).next_watcher[1];
                            ci = *pri;
                        }
                        continue;
                    }
                    debug_assert!((*c).dead);
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
                let c = &mut self.clauses[ci] as *mut Clause;
                if !(*c).dead {
                    // self.print_watcher(0);
                    // self.print_watcher(1);
                    panic!("not dead {:#}", *c);
                }
                debug_assert!((*c).dead);
                // if (*c).index == DEBUG { println!("garbage traverser finds: {:#} on GARBGE link", *c); }
                if (*c).lit[0] == GARBAGE_LIT && (*c).lit[1] == GARBAGE_LIT {
                    // println!("move {} to recycler", (*c).index);
                    // if (*c).index == DEBUG { println!("here comes!"); }
                    let next = (*c).next_watcher[0];
                    *pri = (*c).next_watcher[0];
                    (*c).lit[0] = RECYCLE_LIT;
                    (*c).lit[1] = RECYCLE_LIT;
                    (*c).next_watcher[0] = *recycled;
                    (*c).next_watcher[1] = *recycled;
                    *recycled = ci; // (*c).next_watcher[0];
                    (*c).dead = false;
                    (*c).locked = true;
                    ci = next;
                // print!("recycler: ");
                // self.print_watcher(GARBAGE_LIT.negate());
                } else if (*c).lit[0] != GARBAGE_LIT && (*c).lit[1] != GARBAGE_LIT {
                    println!("very strange {}", *c);
                } else {
                    let index = ((*c).lit[0] != GARBAGE_LIT) as usize; // the other might have still active path
                                                                       // if (*c).index == DEBUG || true { println!("half processed! {:#}", *c); }
                    ci = (*c).next_watcher[index];
                    pri = &mut (*c).next_watcher[index];
                }
            }
        }
        debug_assert_eq!(self.watcher[0], NULL_CLAUSE);
        // ASSERITON
        {
            for i in 2..self.watcher.len() {
                let mut ci = self.watcher[i];
                while ci != NULL_CLAUSE {
                    if self.clauses[ci].dead {
                        panic!("aeaaeamr");
                    }
                    let index = self.clauses[ci].lit[0].negate() != i as Lit;
                    ci = self.clauses[ci].next_watcher[index as usize];
                }
            }
        }
    }
    fn new_clause(&mut self, v: &Vec<Lit>, rank: usize, learnt: bool, locked: bool) -> ClauseId {
        let cix;
        let w0;
        let w1;
        if self.watcher[RECYCLE_LIT.negate() as usize] != NULL_CLAUSE {
            cix = self.watcher[RECYCLE_LIT.negate() as usize];
            debug_assert_eq!(self.clauses[cix].dead, false);
            debug_assert_eq!(self.clauses[cix].lit[0], RECYCLE_LIT);
            debug_assert_eq!(self.clauses[cix].lit[1], RECYCLE_LIT);
            debug_assert_eq!(self.clauses[cix].index, cix);
            self.watcher[RECYCLE_LIT.negate() as usize] = self.clauses[cix].next_watcher[0];
            // reincarnation
            let c = &mut self.clauses[cix];
            c.lit[0] = v[0];
            c.lit[1] = v[1];
            c.lits.clear();
            for l in &v[2..] {
                c.lits.push(*l);
            }
            c.rank = rank;
            c.locked = locked;
            c.learnt = learnt;
            c.just_used = false;
            c.sve_mark = false;
            c.touched = false;
            c.activity = 0.0;
            w0 = c.lit[0].negate() as usize;
            w1 = c.lit[1].negate() as usize;
            c.next_watcher[0] = self.watcher[w0];
            c.next_watcher[1] = self.watcher[w1];
        } else {
            cix = self.clauses.len();
            // make a new clause as c
            let mut c = Clause::new(self.kind, learnt, rank, &v, locked);
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
        // {
        //     let c = &self.clauses[cix];
        //     let l0 = c.lit[0];
        //     if !self.seek_from(cix, l0) {
        //         panic!("NOT FOUND for {} c: {:#}", l0.int(), c);
        //     }
        //     let l1 = c.lit[1];
        //     if !self.seek_from(cix, l1) {
        //         panic!("NOT FOUND for {} c: {:#}", l1.int(), c);
        //     }
        // }
        self.id_from(cix)
    }
    fn id_from(&self, cix: ClauseIndex) -> ClauseId {
        cix | self.tag
    }
    fn index_from(&self, cid: ClauseId) -> ClauseIndex {
        cid & self.mask
    }
    fn len(&self) -> usize {
        self.clauses.len()
    }
    fn count(&self, target: Lit, limit: usize) -> usize {
        let mut ci = self.watcher[target.negate() as usize];
        let mut cnt = 0;
        while ci != NULL_CLAUSE {
            cnt += 1;
            let c = &self.clauses[ci];
            if ci == c.next_watcher[(c.lit[0] != target) as usize] {
                panic!("{} is looping!", target);
            }
            if 0 < limit && limit <= cnt {
                return limit;
            }
            if cnt % 10000 == 0 && false {
                //let cc = &self.clauses[self.watcher[target.negate() as usize]];
                // println!("#{} = {}, {:#}", target, cnt, cc);
                // cc = &self.clauses[cc.next_watcher[(cc.lit[0] != target) as usize]];
                // println!("#{} = {}, {:#}", target, cnt, cc);
            }
            ci = c.next_watcher[(c.lit[0] != target) as usize];
        }
        cnt
    }
}

impl ClausePack {
    pub fn build(i: ClauseKind, nv: usize, nc: usize) -> ClausePack {
        let kind = i;
        let tag = i.tag();
        let mask = i.mask();
        let mut clauses = Vec::with_capacity(1 + nc);
        clauses.push(Clause::null());
        let mut permutation = Vec::new();
        permutation.push(0); // for NULL_CLAUSE
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        for _i in 0..2 * (nv + 1) {
            watcher.push(NULL_CLAUSE);
        }
        ClausePack {
            kind,
            init_size: nc,
            clauses,
            // permutation,
            watcher,
            mask,
            tag,
            index_bits: CLAUSE_INDEX_BITS,
        }
    }
    pub fn attach(&mut self, mut c: Clause) -> ClauseId {
        let w0 = c.lit[0].negate() as usize;
        let w1 = c.lit[1].negate() as usize;
        let cix;
        if self.watcher[RECYCLE_LIT.negate() as usize] == NULL_CLAUSE
            && self.watcher[GARBAGE_LIT.negate() as usize] != NULL_CLAUSE
        {
            self.garbage_collect();
        }
        if self.watcher[RECYCLE_LIT.negate() as usize] != NULL_CLAUSE {
            cix = self.watcher[RECYCLE_LIT.negate() as usize];
            debug_assert_eq!(self.clauses[cix].dead, false);
            debug_assert_eq!(self.clauses[cix].lit[0], RECYCLE_LIT);
            debug_assert_eq!(self.clauses[cix].lit[1], RECYCLE_LIT);
            c.index = cix;
            self.watcher[RECYCLE_LIT.negate() as usize] = self.clauses[cix].next_watcher[0];
            c.next_watcher[0] = self.watcher[w0];
            c.next_watcher[1] = self.watcher[w1];
            // print!("attach use a recycle: ");
            // self.print_watcher(GARBAGE_LIT.negate());
            self.clauses[cix] = c;
        } else {
            cix = self.clauses.len();
            c.index = cix;
            // self.permutation.push(cix);
            c.next_watcher[0] = self.watcher[w0];
            c.next_watcher[1] = self.watcher[w1];
            self.clauses.push(c);
        };
        self.watcher[w0] = cix;
        self.watcher[w1] = cix;

        // {
        //     let c = &self.clauses[cix];
        //     let l0 = c.lit[0];
        //     if !self.seek_from(cix, l0) {
        //         panic!("NOT FOUND for {} c: {:#}", l0.int(), c);
        //     }
        //     let l1 = c.lit[1];
        //     if !self.seek_from(cix, l1) {
        //         panic!("NOT FOUND for {} c: {:#}", l1.int(), c);
        //     }
        // }
        self.id_from(cix)
    }
}

impl ClauseIdIndexEncoding for usize {
    fn to_id(&self) -> ClauseId {
        *self
    }
    fn to_index(&self) -> ClauseIndex {
        (*self & CLAUSE_INDEX_MASK) as usize
    }
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
    pub fn new(
        kind: ClauseKind,
        learnt: bool,
        rank: usize,
        vec: &Vec<Lit>,
        locked: bool,
    ) -> Clause {
        let mut v = vec.clone();
        let lit0 = v.remove(0);
        let lit1 = v.remove(0);
        Clause {
            kind,
            index: 0,
            rank: rank,
            next_watcher: [NULL_CLAUSE; 2],
            lit: [lit0, lit1],
            lits: v,
            dead: false,
            locked,
            learnt,
            just_used: false,
            sve_mark: false,
            touched: false,
            activity: 0.0,
        }
    }
    pub fn null() -> Clause {
        Clause {
            kind: ClauseKind::Permanent,
            index: 0,
            rank: 0,
            next_watcher: [NULL_CLAUSE; 2],
            lit: [NULL_LIT; 2],
            lits: vec![],
            dead: false,
            locked: false,
            learnt: false,
            just_used: false,
            sve_mark: false,
            touched: false,
            activity: 0.0,
        }
    }
    pub fn len(&self) -> usize {
        self.lits.len() + 2
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if f.alternate() {
            write!(
                f,
                "{{C{}:{} lit:{:?}{:?}, watches{:?}{}{}}}",
                self.kind as usize,
                self.index,
                vec2int(&self.lit),
                vec2int(&self.lits),
                self.next_watcher,
                if self.dead { ", dead" } else { "" },
                if self.locked { ", locked" } else { "" },
            )
        } else {
            match self.index {
                //            x if x < 0 => write!(f, format!("a given clause {}", self.lits.map(|l| l.int()))),
                0 => write!(f, "null_clause"),
                DEAD_CLAUSE => {
                    debug_assert!(self.dead);
                    write!(
                        f,
                        "dead{}[{},{}]{:?}",
                        self.index,
                        self.lit[0].int(),
                        self.lit[1].int(),
                        &self.lits.iter().map(|l| l.int()).collect::<Vec<i32>>()
                    )
                }
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

impl ClauseManagement for ClauseDBState {
    fn bump(&mut self, cp: &mut [ClausePack; 3], cid: ClauseId) -> () {
        debug_assert_ne!(cid, 0);
        let a;
        {
            let c = &mut cp[cid.to_kind()].clauses[cid.to_index()];
            //let c = mref!(cp, cid);
            a = c.activity + self.cla_inc;
            c.activity = a;
        }
        if 1.0e20 < a {
            for c in &mut cp[ClauseKind::Removable as usize].clauses {
                if c.learnt {
                    c.activity *= 1.0e-20;
                }
            }
            self.cla_inc *= 1.0e-20;
        }
    }
    fn decay_cla_activity(&mut self) -> () {
        self.cla_inc = self.cla_inc / self.decay_rate;
    }
    /// 1. sort `permutation` which is a mapping: index -> ClauseIndex.
    /// 2. rebuild watches to pick up clauses which is placed in a good place in permutation.
    fn reduce(&mut self, cp: &mut ClausePack, thr: f64) -> () {
        {
            let ClausePack {
                ref mut clauses, ..
            } = cp;
            // debug_assert_eq!(permutation.len(), clauses.len());
            // permutation.retain(|i| !clauses[*i as usize].dead);
            let permutation = &mut (1..clauses.len())
                .filter(|i| !clauses[*i].dead && 1 < clauses[*i].lit[0] && 1 < clauses[*i].lit[1]) // garbage and recycled
                .collect::<Vec<ClauseIndex>>();
            // sort the range of 'permutation'
            let nc = permutation.len();
            if nc == 0 {
                return;
            }
            permutation.sort_by(|&a, &b| clauses[a].cmp(&clauses[b]));
            let keep = nc / 2;
            for i in keep + 1..nc {
                let mut c = &mut clauses[permutation[i]];
                if !c.locked && !c.just_used && thr as usize <= c.rank {
                    c.dead = true;
                }
                c.just_used = false;
            }
        }
        cp.garbage_collect();
    }
    /// call only when decision level is zero; there's no locked clause.
    fn simplify(&mut self, cps: &mut [ClausePack; 3], assign: &Vec<Lbool>) -> bool {
        // find garbages
        for cp in &mut cps[..] {
            let len = cp.watcher.len();
            // let mut garbage = &mut cp.watcher[(GARBAGE_LIT.negate()) as usize];
            for lit in 2..len {
                unsafe {
                    let mut pri = &mut cp.watcher[(lit as Lit).negate() as usize] as *mut ClauseId;
                    let mut garbages =
                        &mut cp.watcher[(GARBAGE_LIT.negate()) as usize] as *mut ClauseId;
                    while *pri != NULL_CLAUSE {
                        let c = &mut cp.clauses[*pri] as *mut Clause;
                        let index = ((*c).lit[0] != lit as Lit) as usize;
                        if (&assign[..]).satisfies(&*c) {
                            (*c).dead = true;
                            *pri = (*garbages).push_garbage(&mut *c, index);
                        // *pri = cp.detach(&mut *c, index);
                        // cp[*ck as usize].check_clause("after GC", (*c).index);
                        } else {
                            pri = &mut (*c).next_watcher[index];
                        }
                    }
                }
            }
            cp.garbage_collect();
        }
        // if self.eliminator.use_elim && self.stats[Stat::NumOfSimplification as usize] % 8 == 0 {
        //     self.eliminate();
        // }
        true
    }
}

/// for ClausePack
pub trait CheckPropagation {
    fn assertion_soundness(&self) -> bool;
    fn check_garbage(&mut self) -> ();
    fn seek_from(&self, ci: ClauseIndex, p: Lit) -> bool;
    fn print_watcher(&self, p: Lit) -> ();
    fn check_clause(&self, mes: &str, ci: ClauseIndex);
    fn check_lit(&self, assign: &Vec<Lbool>, vars: &Vec<Var>, mes: &str, lit: Lit) -> ();
}

impl CheckPropagation for ClausePack {
    fn assertion_soundness(&self) -> bool {
        for c in &self.clauses[1..] {
            if !self.seek_from(c.index, c.lit[0]) {
                if !(c.dead && c.lit[0] == GARBAGE_LIT && c.lit[1] == GARBAGE_LIT) {
                    println!("0: {:#}", c);
                    self.print_watcher(GARBAGE_LIT);
                    return false;
                } else if c.dead {
                    self.print_watcher(GARBAGE_LIT);
                }
            }
            if !self.seek_from(c.index, c.lit[1]) {
                if !(c.dead && c.lit[0] == GARBAGE_LIT && c.lit[1] == GARBAGE_LIT) {
                    println!("1: {:#}", c);
                    self.print_watcher(GARBAGE_LIT);
                    return false;
                } else if c.dead {
                    self.print_watcher(GARBAGE_LIT);
                }
            }
        }
        true
    }
    fn check_garbage(&mut self) -> () {
        {
            for c in &self.clauses[1..] {
                if c.dead {
                    panic!(
                        "fail to gather all garbages. An exception {:#} {}, {}",
                        c,
                        self.seek_from(c.index, c.lit[0]),
                        self.seek_from(c.index, c.lit[1]),
                    );
                }
            }
        }
    }
    // returns false when error.
    fn seek_from(&self, ci: ClauseIndex, p: Lit) -> bool {
        let mut i = self.watcher[p.negate() as usize];
        while i != NULL_CLAUSE {
            let c = &self.clauses[i];
            if c.index == ci {
                return true;
            }
            let index = if c.lit[0] == p { 0 } else { 1 };
            i = c.next_watcher[index];
        }
        false
    }
    fn print_watcher(&self, p: Lit) -> () {
        match p {
            GARBAGE_LIT => print!("watcher[garbage] = "),
            RECYCLE_LIT => print!("watcher[recycle] = "),
            x => print!("watcher[{}] = ", x.int()),
        };
        let mut i = self.watcher[p as usize];
        while i != NULL_CLAUSE {
            let c = &self.clauses[i];
            print!("{}, ", i);
            let index = match () {
                _ if c.lit[0].negate() == p => 0,
                _ if c.lit[1].negate() == p => 1,
                _ => panic!("the literal {} is not a watcher for {:#}", p, c),
            };
            i = c.next_watcher[index];
        }
        println!("0");
    }
    fn check_clause(&self, mes: &str, ci: ClauseIndex) {
        if ci != DEBUG {
            return;
        }
        let c = &self.clauses[DEBUG];
        let l0 = c.lit[0];
        let l1 = c.lit[1];
        let r0 = self.seek_from(c.index, l0);
        let r1 = self.seek_from(c.index, l1);
        if r0 || r1 {
            println!(
                "No problem on watchers of {} clause {} '{}'; watching {} and {}",
                if c.dead { "dead" } else { "" },
                ci,
                mes,
                l0.show(),
                l1.show()
            );
        } else {
            println!(
                "Assersion failed by {} at '{}', lit0({}): {}, lit1({}): {}",
                c.index,
                mes,
                l0.show(),
                r0,
                l1.show(),
                r1,
            );
            self.print_watcher(l0.negate());
            self.print_watcher(l1.negate());
            println!("{:#}", c);
            panic!("panic");
        }
    }
    fn check_lit(&self, assign: &Vec<Lbool>, vars: &Vec<Var>, mes: &str, lit: Lit) -> () {
        let vi = lit.vi();
        if vi == WATCHING {
            let p = vi.lit(LTRUE);
            let n = vi.lit(LFALSE);
            let found_in_p = self.seek_from(DEBUG, p);
            let found_in_n = self.seek_from(DEBUG, n);
            if (p.lbool() == vars[vi].phase || p.lbool() == assign[vi])
                && !found_in_p
                && !found_in_n
            {
                return;
            }
            if found_in_p || found_in_n {
                println!("Watcher state: {} on {}", mes, lit.int());
                if found_in_p {
                    print!(" - ");
                    self.print_watcher(n);
                }
                if found_in_n {
                    print!(" - ");
                    self.print_watcher(p);
                }
            }
            println!(
                "Check lit: {} on {} not including C{}",
                mes,
                lit.int(),
                DEBUG
            );
        }
    }
}

impl<'a> ClauseList for ClauseIndex {
    fn push(&mut self, cix: ClauseIndex, item: &mut ClauseIndex) -> ClauseIndex {
        *item = *self;
        *self = cix;
        *item
    }
    fn push_garbage(&mut self, c: &mut Clause, index: usize) -> ClauseIndex {
        let other = (index ^ 1) as usize;
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

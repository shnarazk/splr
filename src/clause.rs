use std::cmp::Ordering;
use std::f64;
use std::fmt;
use std::usize::MAX;
use types::*;

const CLAUSE_INDEX_BITS: usize = 60;
const CLAUSE_INDEX_MASK: usize = 0x0FFF_FFFF_FFFF_FFFF;
pub const DEAD_CLAUSE: usize = MAX;

pub const RANK_NULL: usize = 0; // for NULL_CLAUSE
pub const RANK_CONST: usize = 1; // for given clauses
pub const RANK_NEED: usize = 2; // for newly generated bi-clauses

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
    pub init_size: usize,
    pub clauses: Vec<Clause>,
    pub permutation: Vec<ClauseIndex>,
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

pub trait ClauseIdIndexEncoding {
    fn to_id(&self) -> ClauseId;
    fn to_index(&self) -> ClauseIndex;
    fn to_kind(&self) -> usize;
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

impl ClausePack {
    pub fn build(i: ClauseKind, nv: usize, nc: usize) -> ClausePack {
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
            init_size: nc,
            clauses,
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
        let cix;
        if self.watcher[0] != NULL_CLAUSE {
            cix = self.watcher[0];
            debug_assert_eq!(self.clauses[cix].dead, false);
            c.index = cix;
            self.watcher[0] = self.clauses[cix].next_watcher[0];
            c.next_watcher[0] = self.watcher[w0];
            c.next_watcher[1] = self.watcher[w1];
            self.clauses[cix] = c;
        } else {
            cix = self.clauses.len();
            c.index = cix;
            self.permutation.push(cix);
            c.next_watcher[0] = self.watcher[w0];
            c.next_watcher[1] = self.watcher[w1];
            self.clauses.push(c);
        };
        self.watcher[w0] = cix;
        self.watcher[w1] = cix;
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
    pub fn new(kind: ClauseKind, learnt: bool, rank: usize, mut v: Vec<Lit>) -> Clause {
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
            locked: false,
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
            rank: RANK_NULL,
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
                "C{} rank:{}, activity: {}, lit:{:?}{:?}",
                self.index, self.rank, self.activity, vec2int(self.lit.clone().to_vec()), vec2int(self.lits.clone().to_vec()),
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

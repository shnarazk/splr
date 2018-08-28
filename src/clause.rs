use std::cmp::Ordering;
use std::f64;
use std::fmt;
use types::*;

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

#[derive(Clone, Copy, Debug)]
pub enum ClauseKind {
    Removable = 0,
    Permanent,
    Binclause,
}

const CLAUSE_INDEX_BITS: usize = 60;
const CLAUSE_INDEX_MASK: usize = 0x0FFF_FFFF_FFFF_FFFF;

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
        let mut permutation = Vec::with_capacity(1 + nc);
        for _i in 0..1 + nc {
            permutation.push(NULL_CLAUSE);
        }
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
        let cix = self.clauses.len();
        c.index = cix;
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
}

pub const RANK_NULL: usize = 0; // for NULL_CLAUSE
pub const RANK_CONST: usize = 1; // for given clauses
pub const RANK_NEED: usize = 2; // for newly generated bi-clauses

/// Clause Index, not ID because it's used only within a Vec<Clause>
pub type ClauseIndex = usize;

pub trait ClauseIdIndexEncoding {
    fn to_id(&self) -> ClauseId;
    fn to_index(&self) -> ClauseIndex;
    fn to_kind(&self) -> usize;
}

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
    /// used for a reason of propagation
    pub locked: bool,
    /// given or learnt
    pub learnt: bool,
    /// used in the current phase
    pub just_used: bool,
    /// used in Subsumption Variable Eliminator
    pub sve_mark: bool,
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
            return Some(Ordering::Less);
        } else if self.rank > other.rank {
            return Some(Ordering::Greater);
        } else if self.activity > other.activity {
            return Some(Ordering::Less);
        } else if self.activity < other.activity {
            return Some(Ordering::Greater);
        } else {
            return Some(Ordering::Equal);
        }
    }
}

impl Ord for Clause {
    fn cmp(&self, other: &Clause) -> Ordering {
        if self.rank < other.rank {
            return Ordering::Less;
        } else if self.rank > other.rank {
            return Ordering::Greater;
        } else if self.activity > other.activity {
            return Ordering::Less;
        } else if self.activity < other.activity {
            return Ordering::Greater;
        } else {
            return Ordering::Equal;
        }
    }
}

impl Clause {
    pub fn new(kind: ClauseKind, learnt: bool, rank: usize, mut v: Vec<Lit>) -> Clause {
        let lit0 = v.remove(0);
        let lit1 = v.remove(0);
        Clause {
            kind,
            learnt,
            activity: 0.0,
            rank: rank,
            next_watcher: [NULL_CLAUSE; 2],
            lit: [lit0, lit1],
            lits: v,
            index: 0,
            locked: false,
            just_used: false,
            sve_mark: false,
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
            locked: false,
            learnt: false,
            just_used: false,
            sve_mark: false,
        }
    }
    pub fn len(&self) -> usize {
        self.lits.len() + 2
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.index {
            //            x if x < 0 => write!(f, format!("a given clause {}", self.lits.map(|l| l.int()))),
            0 => write!(f, "null_clause"),
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
                &self.lits.iter().map(|l| l.int()).collect::<Vec<i32>>()
            ),
        }
    }
}

pub fn cid2fmt(cid: ClauseId) -> String {
    match cid >> CLAUSE_INDEX_BITS {
        0 => format!("[learnt:{}]", cid.to_index()),
        _ => format!("[prmnnt:{}]", cid.to_index()),
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
}

// impl Clause {
//     void calcAbstraction() {
//         assert(header.extra_size > 0);
//         uint32_t abstraction = 0;
//         for (int i = 0; i < size(); i++)
//             abstraction |= 1 << (var(data[i].lit) & 31);
//         data[header.size].abs = abstraction;  }
// }
//  inline void Clause::strengthen(Lit p)
//  {
//      remove(*this, p);
//      calcAbstraction();
//  }

impl Dump for [ClausePack] {
    fn dump(&self, str: &str) -> () {
        println!("dumped {}", str);
    }
}

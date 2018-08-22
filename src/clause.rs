use std::cmp::Ordering;
use std::f64;
use std::fmt;
use types::*;

pub const KERNEL_CLAUSE: usize = 0x8000_0000_0000_0000;
const INDEX_MASK: usize = 0x7FFF_FFFF_FFFF_FFFF;
pub const CID2KIND: usize = 63;

pub const RANK_NULL: usize = 0; // for NULL_CLAUSE
pub const RANK_CONST: usize = 1; // for given clauses
pub const RANK_NEED: usize = 2; // for newly generated bi-clauses

/// Clause Index, not ID because it's used only within a Vec<Clause>
pub type ClauseIndex = usize;

pub trait ClauseIdIndexEncoding {
    fn is_learnt(&self) -> bool;
    fn to_id(&self) -> ClauseId;
    fn to_index(&self) -> ClauseIndex;
    fn to_kind(&self) -> usize;
    fn as_permanent_id(&self) -> ClauseId;
    fn as_deletable_id(&self) -> ClauseId;
}

/// Clause
#[derive(Debug)]
pub struct Clause {
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
    /// cache for propagation
    pub swap: usize,
}

impl ClauseIdIndexEncoding for usize {
    fn is_learnt(&self) -> bool {
        *self & KERNEL_CLAUSE == 0
    }
    fn to_id(&self) -> ClauseId {
        *self
    }
    #[inline]
    fn to_index(&self) -> ClauseIndex {
        (*self & INDEX_MASK) as usize
    }
    #[inline]
    fn to_kind(&self) -> usize {
        *self >> CID2KIND
    }
    fn as_permanent_id(&self) -> ClauseId {
        *self | KERNEL_CLAUSE
    }
    fn as_deletable_id(&self) -> ClauseId {
        *self & INDEX_MASK
    }
}

impl ClauseIdIndexEncoding for Clause {
    fn is_learnt(&self) -> bool {
        self.learnt
    }
    fn to_id(&self) -> ClauseId {
        if self.learnt && 2 < self.lits.len() {
            self.index + KERNEL_CLAUSE
        } else {
            self.index
        }
    }
    fn to_index(&self) -> ClauseIndex {
        self.index
    }
    fn to_kind(&self) -> usize {
        (!self.learnt || 2 == self.lits.len()) as usize
    }
    fn as_permanent_id(&self) -> ClauseId {
        self.index | KERNEL_CLAUSE
    }
    fn as_deletable_id(&self) -> ClauseId {
        self.index & INDEX_MASK
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
    pub fn new(learnt: bool, rank: usize, mut v: Vec<Lit>) -> Clause {
        let lit0 = v.remove(0);
        let lit1 = v.remove(0);
        Clause {
            activity: 0.0,
            rank: rank,
            next_watcher: [NULL_CLAUSE; 2],
            lit: [lit0, lit1],
            lits: v,
            index: 0,
            locked: false,
            learnt: learnt,
            swap: 0,
        }
    }
    pub fn null() -> Clause {
        Clause {
            activity: 0.0,
            rank: RANK_NULL,
            next_watcher: [NULL_CLAUSE; 2],
            lit: [NULL_LIT; 2],
            lits: vec![],
            index: 0,
            locked: false,
            learnt: false,
            swap: 0,
        }
    }
    pub fn len(&self) -> usize {
        self.lits.len()
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
                if self.is_learnt() { 'L' } else { 'P' },
                self.index,
                self.lit[0].int(),
                self.lit[1].int(),
                &self.lits.iter().map(|l| l.int()).collect::<Vec<i32>>()
            ),
        }
    }
}

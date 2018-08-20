use std::cmp::Ordering;
use std::f64;
use std::fmt;
use types::*;

pub const RANK_NULL: usize = 0; // for NULL_CLAUSE
pub const RANK_CONST: usize = 1; // for given clauses
pub const RANK_NEED: usize = 2; // for newly generated bi-clauses

/// Clause
/// Clause should be placed on heap anytime.
/// And `Box` provides Eq for 'clause pointer'.
#[derive(Debug)]
pub struct Clause {
    /// a temporal index which is equal to the index for `clauses` or `learnts`
    pub index: ClauseIndex,
    /// clause activity used by `analyze` and `reduce_db`
    pub activity: f64,
    /// LBD or NDD and so on, used by `reduce_db`
    pub rank: usize,
    /// the literals
    pub lits: Vec<Lit>,
    /// used for a reason of propagation
    pub locked: bool,
    /// given or learnt
    pub learnt: bool,
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
    pub fn new(rank: usize, v: Vec<Lit>) -> Clause {
        Clause {
            activity: 0.0,
            rank: rank,
            lits: v,
            index: 0,
            locked: false,
            learnt: RANK_CONST < rank,
        }
    }
    pub fn null() -> Clause {
        Clause {
            activity: 0.0,
            rank: RANK_NULL,
            lits: vec![],
            index: 0,
            locked: false,
            learnt: false,
        }
    }
    pub fn len(&self) -> usize {
        self.lits.len()
    }
    pub fn watch0(&self) -> Lit {
        self.lits[0]
    }
    pub fn watch1(&self) -> Lit {
        self.lits[1]
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.index {
            //            x if x < 0 => write!(f, format!("a given clause {}", self.lits.map(|l| l.int()))),
            0 => write!(f, "null_clause"),
            _ => write!(
                f,
                "C{}{:?}",
                self.index,
                &self.lits.iter().map(|l| l.int()).collect::<Vec<i32>>()
            ),
        }
    }
}

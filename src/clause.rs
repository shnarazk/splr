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
    /// temporal field for `sort_clause` and `propagate`
    pub tmp: usize,
}

///```
///    # use splr::types::*;
///    let c1 = splr::clause::Clause::new(3, vec![int2lit(1), int2lit(2), int2lit(3)]);
///    let mut c2 = splr::clause::Clause::new(2, vec![int2lit(-1), int2lit(4)]);
///    c2.index = 2;
///    c2.activity = 2.4;
///    assert_eq!(c1, c1);
///    assert_eq!(c1 == c1, true);
///    assert_ne!(c1, c2);
///    assert_eq!(c2.activity, 2.4);
///```
impl PartialEq for Clause {
    fn eq(&self, other: &Clause) -> bool {
        self.index == other.index
    }
}

impl Eq for Clause {}

impl PartialOrd for Clause {
    /// the key is `tmp`, not `rank`, since we want to reflect whether it's used as a reason.
    fn partial_cmp(&self, other: &Clause) -> Option<Ordering> {
        if self.tmp < other.tmp {
            return Some(Ordering::Less);
        } else if self.tmp > other.tmp {
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
        if self.tmp < other.tmp {
            return Ordering::Less;
        } else if self.tmp > other.tmp {
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
            tmp: 0,
        }
    }
    pub fn null() -> Clause {
        Clause {
            activity: 0.0,
            rank: RANK_NULL,
            lits: vec![],
            index: 0,
            tmp: 0,
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

/// Only ClauseExtManager is the owner of clauses.
/// Other functions should borrow a mutual reference from it.
pub type ClauseManager = Vec<Clause>;

/// returns a new clause manager.
pub fn new_clause_manager(nc: usize) -> ClauseManager {
    let mut m = Vec::with_capacity(1 + nc);
    m.push(Clause::null());
    m
}

pub fn vec2int(v: Vec<Lit>) -> Vec<i32> {
    v.iter().map(|l| l.int()).collect::<Vec<i32>>()
}

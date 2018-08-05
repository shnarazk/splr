#![allow(dead_code)]
#![allow(unused_imports)]
use std::fmt;
use types::*;

/// Clause Index, not ID because it changes after database reduction.
/// # Range
/// * `< 0` for given clauses
/// * 0 for a null clause
/// * '0 <' for learnt clauses
pub type ClauseIndex = isize;

pub const NULL_CLAUSE: ClauseIndex = 0;

/// Clause
/// Clause should be placed on heap anytime.
/// And `Box` provides Eq for 'clause pointer'.
pub struct Clause {
    pub activity: f64,
    pub rank: usize,
    pub lits: Vec<Lit>,
    pub index: isize,
}

impl Clause {
    pub fn new(v: Vec<Lit>) -> Clause {
        Clause {
            activity: 0.0,
            rank: v.len(),
            lits: v,
            index: 0,
        }
    }
    pub fn null() -> Clause {
        Clause {
            activity: 0.0,
            rank: 0,
            lits: vec![],
            index: 0,
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

impl PartialEq for Clause {
    fn eq(&self, other: &Clause) -> bool {
        self.lits == other.lits
    }
}

impl Eq for Clause {}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.lits.len() {
            0 => write!(f, "null_clause"),
            2 => write!(f, "a biclause"),
            _ => write!(f, "a clause"),
        }
    }
}

/// Only ClauseExtManager is the owner of clauses.
/// Other functions should borrow a mutual reference from it.
pub type ClauseManager = Vec<(i32, Box<Clause>)>;

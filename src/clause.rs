#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use std::fmt;
use types::*;

/// Clause Index, not ID because it changes after database reduction.
/// # Range
/// * `< 0` for given clauses. So we need `isize` instead of `usize`
/// * 0 for a null clause
/// * '0 <' for learnt clauses
pub type ClauseIndex = isize;

pub const NULL_CLAUSE: ClauseIndex = 0;

/// Clause
/// Clause should be placed on heap anytime.
/// And `Box` provides Eq for 'clause pointer'.
pub struct Clause {
    /// a temporal index which is equal to the index for `clauses` or `learnts`
    pub index: ClauseIndex,
    /// clause activity used by `analyze` and `reduce_db`
    pub activity: f64,
    /// LBD or NDD and so on, used by `reduce_db`
    pub rank: usize,
    /// the literals
    pub lits: Vec<Lit>,
}

impl Drop for Clause {
    fn drop(&mut self) {
        match self.index {
            x if x < 0 => println!("Drop a given clause!!"),
            x if 0 < x => println!("Drop a learnt clause!!"),
            _ => println!("Null is removed."),
        }
    }
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
pub type ClauseManager = Vec<Clause>;

pub fn new_clause_maanager() -> ClauseManager {
    let mut m = Vec::new();
    m.push(Clause::null());
    m
}

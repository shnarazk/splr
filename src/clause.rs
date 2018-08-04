#![allow(dead_code)]
#![allow(unused_imports)]
use std::fmt;
use types::*;

/// Clause
/// Clause should be placed on heap anytime.
/// And `Box` provides Eq for 'clause pointer'.
pub struct Clause {
    pub activity: f64,
    pub rank: usize,
    pub lits: Vec<Lit>,
}

impl Clause {
    pub fn new(v: Vec<Lit>) -> Clause {
        Clause {
            activity: 0.0,
            rank: v.len(),
            lits: v,
        }
    }
    pub fn null() -> Clause {
        Clause {
            activity: 0.0,
            rank: 0,
            lits: vec![],
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
pub type ClauseManager = Vec<(i32, Clause)>;

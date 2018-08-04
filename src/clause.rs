#![allow(dead_code)]
#![allow(unused_imports)]
use std::fmt;
use types::*;

/// Clause
/// Clause should be placed on heap anytime.
/// And `Box` provides Eq for 'clause pointer'.
pub struct Clause {
    pub activity: f64,
    pub rank: i32,
    pub lits: Vec<Lit>,
}

impl Clause {
    pub fn new(v: Vec<Lit>) -> Clause {
        Clause {
            activity: 0.0,
            rank: v.len() as i32,
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

/// ClauseExtManager is only the owner of clauses.
/// Other functions should borrow a mutual reference from it.
pub struct ClauseManager {
    num_actives: usize, // the number of active clause
    purged: bool,       // whether it needs gc
    clauses: Vec<Box<Clause>>,
    keys: Vec<i32>,
}

impl ClauseManager {
    pub fn new() -> ClauseManager {
        ClauseManager {
            num_actives: 0,
            purged: false,
            clauses: vec![],
            keys: vec![],
        }
    }
    pub fn shrink(&mut self, k: usize) -> () {
        self.num_actives -= k
    }
    pub fn push(&mut self, c: Box<Clause>) -> () {
        self.clauses.push(c);
        self.keys.push(0);
    }
    pub fn pop(&mut self) -> () {
        self.num_actives -= 1
    }
    pub fn last(&mut self) -> &mut Box<Clause> {
        &mut (self.clauses[self.num_actives - 1])
    }
}

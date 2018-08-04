#![allow(dead_code)]
#![allow(unused_imports)]
use std::fmt;
use types::*;

/// Clause Id
pub type CID = usize;

/// Clause
/// Clause should be placed on heap anytime.
/// And `Box` provides Eq for 'clause pointer'.
pub struct Clause {
    pub cid: CID,
    pub activity: f64,
    pub rank: usize,
    pub lits: Vec<Lit>,
}

impl Clause {
    pub fn new(k: usize, v: Vec<Lit>) -> Clause {
        Clause {
            cid: k,
            activity: 0.0,
            rank: v.len(),
            lits: v,
        }
    }
    pub fn null() -> Clause {
        Clause {
            cid: 0,
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
pub struct ClauseManager {
    pub id2index: Vec<usize>,
    pub vec: Vec<(i32, Box<Clause>)>,
}

impl ClauseManager {
    pub fn new(n: usize) -> ClauseManager {
        let mut t = Vec::new();
        t.reserve(n);
        let mut v = Vec::new();
        v.reserve(n);
        ClauseManager {
            id2index: t,
            vec: v,
        }
    }
    pub fn push(&mut self, k: i32, c: Clause) -> () {
        let v = &mut self.vec;
        let cid = c.cid;
        v.push((k, Box::new(c)));
        let index = v.len() - 1;
        let t = &mut self.id2index;
        if t.len() <= cid {
            t.resize(cid + 10, 0)
        };
        t[cid] = index;
    }
    pub fn from_id(&self, i: usize) -> &(i32, Box<Clause>) {
        &self.vec[self.id2index[i]]
    }
}

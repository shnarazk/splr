#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use std::cmp::min;
use std::cmp::Ordering;
use std::f64;
use std::fmt;
use types::*;

const RANK_WIDTH: i64 = 11;
const ACTIVITY_WIDTH: i64 = 51;
const RANK_MAX: i64 = 2000;
const ACTIVITY_MAX: i64 = 2 ^ ACTIVITY_WIDTH - 1;

/// Clause Index, not ID because it changes after database reduction.
/// # Range
/// * `< 0` for given clauses. So we need `i64` instead of `usize`
/// * 0 for a null clause
/// * '0 <' for learnt clauses
pub type ClauseIndex = i64;

pub const NULL_CLAUSE: ClauseIndex = 0;

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
    pub tmp: i64,
}

#[cfg(drop)]
impl Drop for Clause {
    fn drop(&mut self) {
        match self.index {
            x if x < 0 => println!("Drop a given clause {}", self),
            x if 0 < x => println!("Drop a learnt clause!! {}", self),
            _ => println!("Null is removed."),
        }
    }
}

impl Clause {
    pub fn new(mut v: Vec<Lit>) -> Clause {
        v.sort();
        Clause {
            activity: 0.0,
            rank: v.len(),
            lits: v,
            index: 0,
            tmp: 0,
        }
    }
    pub fn null() -> Clause {
        Clause {
            activity: 0.0,
            rank: 0,
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
    /// returns 1 if this is good enough.
    pub fn set_sort_key(&mut self, at: f64) -> usize {
        let k = self.lits.len();
        if k == 2 {
            self.tmp = 0;
            1
        } else {
            let ac = self.activity;
            let d = if ac < at {
                RANK_MAX // bigger is worse
            } else {
                min(RANK_MAX, self.rank as i64)
            };
            self.tmp = d << ACTIVITY_WIDTH + scale_activity(ac);
            0
        }
    }
}

fn scale_activity(x: f64) -> i64 {
    if x < 1e-20 {
        ACTIVITY_MAX
    } else {
        (ACTIVITY_MAX * ((1.0 - (x * 1e20).log10() / 40.0) as i64))
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

pub fn new_clause_manager() -> ClauseManager {
    let mut m = Vec::new();
    m.push(Clause::null());
    m
}

#[derive(Debug)]
pub struct Var {
    pub index: usize,
    pub assign: Lbool,
    pub phase: Lbool,
    pub reason: ClauseIndex,
    pub level: usize,
    pub activity: f64,
}

pub const NULL_VAR: VarIndex = 0;

impl Var {
    pub fn new(i: usize) -> Var {
        Var {
            index: i,
            assign: BOTTOM,
            phase: BOTTOM,
            reason: NULL_CLAUSE,
            level: 0,
            activity: 0.0,
        }
    }
    pub fn new_vars(n: usize) -> Vec<Var> {
        let mut v = Vec::new();
        for i in 0..n + 1 {
            v.push(Var::new(i));
        }
        v
    }
}

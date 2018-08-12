use std::f64;
use std::fmt;
use types::*;

/// Clause Index, not ID because it changes after database reduction.
/// # Range
/// * `< 0` for given clauses. So we need `i64` instead of `usize`.
/// * 0 for a null clause.
/// * '0 <' for learnt clauses.
pub type ClauseIndex = usize;

/// is a dummy clause index
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
    pub tmp: usize,
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
    pub fn new(learnt: bool, v: Vec<Lit>) -> Clause {
        Clause {
            activity: 0.0,
            rank: if learnt { v.len() } else { 0 },
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

/// returns a new clause manager.
pub fn new_clause_manager(nc: usize) -> ClauseManager {
    let mut m = Vec::with_capacity(1 + nc);
    m.push(Clause::null());
    m
}

/// Struct for a variable.
#[derive(Debug)]
pub struct Var {
    pub index: usize,
    pub assign: Lbool,
    pub phase: Lbool,
    pub reason: ClauseIndex,
    pub level: usize,
    pub activity: f64,
}

/// is the dummy var index.
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
        let mut vec = Vec::new();
        for i in 0..n + 1 {
            let mut v = Var::new(i);
            v.activity = (n - i) as f64;
            vec.push(v);
        }
        vec
    }
}

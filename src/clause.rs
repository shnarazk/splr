use std::f64;
use std::fmt;
use types::*;

pub const RANK_CONST: usize = 0;
pub const RANK_NEED: usize = 1;

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
            rank: if learnt { v.len() } else { RANK_CONST },
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

///```
///    # use splr::types::*;
///    let c1 = splr::clause::Clause::new(false, vec![int2lit(1), int2lit(2), int2lit(3)]);
///    let mut c2 = splr::clause::Clause::new(false, vec![int2lit(-1), int2lit(4)]);
///    c2.activity = 2.4;
///    assert_eq!(c1, c1);
///    assert_eq!(c1 == c1, true);
///    assert_ne!(c1, c2);
///    assert_eq!(c2.activity, 2.4);
///```
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

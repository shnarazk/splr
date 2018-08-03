use std::fmt;
use types::*;

/// Clause
pub enum ClauseKind {
    /// Normal clause
    Clause {
        activity: f64,
        rank: i32,
        lits: Vec<Lit>,
    },
    /// Binary clause
    BiClause(Lit, Lit),
}

impl ClauseKind {
    /// Clause should be placed on heap anytime.
    pub fn new(v: Vec<Lit>) -> Box<ClauseKind> {
        Box::new(ClauseKind::Clause {
            activity: 0.0,
            rank: 0,
            lits: v,
        })
    }
    pub fn new2(l1: Lit, l2: Lit) -> Box<ClauseKind> {
        Box::new(ClauseKind::BiClause(l1, l2))
    }
}

pub const CLAUSE0: ClauseKind = ClauseKind::BiClause(0, 0);

impl PartialEq for ClauseKind {
    fn eq(&self, other: &ClauseKind) -> bool {
        match &self {
            ClauseKind::Clause { lits: p, .. } => match &other {
                ClauseKind::Clause { lits: q, .. } => p == q,
                ClauseKind::BiClause(_, _) => false,
            },
            ClauseKind::BiClause(l1, l2) => match &other {
                ClauseKind::Clause { .. } => false,
                ClauseKind::BiClause(l3, l4) => l1 == l3 && l2 == l4,
            },
        }
    }
}

impl Eq for ClauseKind {}

impl fmt::Display for ClauseKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            ClauseKind::Clause { lits: _, .. } => write!(f, "a clause"),
            ClauseKind::BiClause(0, 0) => write!(f, "null_clause"),
            ClauseKind::BiClause(_, _) => write!(f, "a biclause"),
        }
    }
}

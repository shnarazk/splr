use std::fmt;
use types::*;

/// Clause
pub enum ClauseKind {
    /// NullClause as a placeholder
    NullClause,
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
    pub fn new(v: Vec<Lit>) -> ClauseKind {
        ClauseKind::Clause {
            activity: 0.0,
            rank: 0,
            lits: v,
        }
    }
    pub fn new2(l1: Lit, l2: Lit) -> ClauseKind {
        ClauseKind::BiClause(l1, l2)
    }
}

impl PartialEq for ClauseKind {
    fn eq(&self, other: &ClauseKind) -> bool {
        match &self {
            ClauseKind::NullClause => match &other {
                ClauseKind::NullClause => true,
                ClauseKind::Clause { .. } => false,
                ClauseKind::BiClause(_, _) => false,
            },
            ClauseKind::Clause { lits: p, .. } => match &other {
                ClauseKind::NullClause => false,
                ClauseKind::Clause { lits: q, .. } => p == q,
                ClauseKind::BiClause(_, _) => false,
            },
            ClauseKind::BiClause(l1, l2) => match &other {
                ClauseKind::NullClause => false,
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
            ClauseKind::NullClause => write!(f, "Null"),
            ClauseKind::Clause { .. } => write!(f, "a clause"),
            ClauseKind::BiClause(_, _) => write!(f, "a biclause"),
        }
    }
}

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
    // Binary clause
    // BiClause(Lit, Lit),
}

impl PartialEq for ClauseKind {
    fn eq(&self, ref other : &ClauseKind) -> bool {
        match &self {
            ClauseKind::NullClause => match other {
                ClauseKind::NullClause => true,
                _                      => false,
            }
            ClauseKind::Clause { lits: v1, .. } => match &other {
                ClauseKind::NullClause => false,
                ClauseKind::Clause { lits: v2, .. } => v1 == v2,
            }
        }
    }
}

impl Eq for ClauseKind {}

impl fmt::Display for ClauseKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            ClauseKind::NullClause => write!(f, "Null"),
            ClauseKind::Clause { .. } => write!(f, "a clause"),
//            ClauseKind::BiClause(_, _) => write!(f, "a biclause"),
        }
    }
}

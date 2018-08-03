use std::fmt;
use types::*;

/// Clause
pub enum ClauseKind {
    /// NullClause as a placeholder
    NullClause,
    /// Normal clause
    Clause { activity : f64, rank : i32, lits: Vec<Lit> },
    /// Binary clause
    BiClause(Lit, Lit),
}

impl fmt::Display for ClauseKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            ClauseKind::NullClause    => write!(f, "Null"),
            ClauseKind::Clause{..}    => write!(f, "a clause"),
            ClauseKind::BiClause(_,_) => write!(f, "a biclause")
        }
    }
}

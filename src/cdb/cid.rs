use {super::ClauseId, std::fmt};

/// API for Clause Id.
pub trait ClauseIdIF {
    /// return `true` if a given clause id is made from a `Lit`.
    fn is_lifted_lit(self) -> bool;
}

const NULL_CLAUSE: ClauseId = ClauseId { ordinal: 0 };

impl Default for ClauseId {
    #[inline]
    /// return the default empty clause, used in a reason slot or no conflict path.
    fn default() -> Self {
        NULL_CLAUSE
    }
}

impl From<usize> for ClauseId {
    #[inline]
    fn from(u: usize) -> ClauseId {
        ClauseId { ordinal: u as u32 }
    }
}

impl fmt::Display for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if *self == ClauseId::default() {
            write!(f, "NullClause")
        } else {
            write!(f, "{}C", self.ordinal)
        }
    }
}

impl ClauseIdIF for ClauseId {
    /// return `true` if the clause is generated from a literal by Eliminator.
    fn is_lifted_lit(self) -> bool {
        0 != 0x8000_0000 & self.ordinal
    }
}

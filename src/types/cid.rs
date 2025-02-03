use std::{fmt, num::NonZeroU32};

/// API for Clause Id.
pub trait ClauseIdIF {
    /// return `true` if a given clause id is made from a `Lit`.
    fn is_lifted_lit(&self) -> bool;
}

/// Clause identifier, or clause index, starting with one.
/// Note: ids are re-used after 'garbage collection'.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ClauseId {
    /// a sequence number.
    pub ordinal: NonZeroU32,
}

impl Default for ClauseId {
    #[inline]
    /// return the default empty clause, used in a reason slot or no conflict path.
    fn default() -> Self {
        ClauseId {
            ordinal: unsafe { NonZeroU32::new_unchecked(0x7FFF_FFFF) },
        }
    }
}

impl From<usize> for ClauseId {
    #[inline]
    fn from(u: usize) -> ClauseId {
        ClauseId {
            ordinal: unsafe { NonZeroU32::new_unchecked(u as u32) },
        }
    }
}

impl From<ClauseId> for usize {
    #[inline]
    fn from(cid: ClauseId) -> usize {
        NonZeroU32::get(cid.ordinal) as usize
    }
}

impl fmt::Debug for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}C", self.ordinal)
    }
}

impl fmt::Display for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}C", self.ordinal)
    }
}

impl ClauseIdIF for ClauseId {
    /// return `true` if the clause is generated from a literal by Eliminator.
    fn is_lifted_lit(&self) -> bool {
        0 != 0x8000_0000 & NonZeroU32::get(self.ordinal)
    }
}

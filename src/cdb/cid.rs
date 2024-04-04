use {
    super::ClauseRef,
    std::{fmt, num::NonZeroU32},
};

/// API for Clause Id.
pub trait ClauseRefIF {
    /// return `true` if the clause is generated from a literal by Eliminator.
    fn is_lifted_lit(&self) -> bool;
}

impl Default for ClauseRef {
    #[inline]
    /// return the default empty clause, used in a reason slot or no conflict path.
    fn default() -> Self {
        ClauseRef {
            ordinal: unsafe { NonZeroU32::new_unchecked(0x7FFF_FFFF) },
        }
    }
}

impl From<usize> for ClauseRef {
    #[inline]
    fn from(u: usize) -> ClauseRef {
        ClauseRef {
            ordinal: unsafe { NonZeroU32::new_unchecked(u as u32) },
        }
    }
}

impl From<ClauseRef> for usize {
    #[inline]
    fn from(cid: ClauseRef) -> usize {
        NonZeroU32::get(cid.ordinal) as usize
    }
}

impl fmt::Debug for ClauseRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}C", self.ordinal)
    }
}

impl fmt::Display for ClauseRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}C", self.ordinal)
    }
}

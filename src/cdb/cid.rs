use {
    super::{ClauseId, Lit},
    std::{fmt, num::NonZeroU32},
};

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

pub trait LiftedClauseIdIF {
    /// return `true` if the clause is generated from a literal by Eliminator.
    fn is_lifted(&self) -> bool;
    fn lift(lit: &Lit) -> Self;
    fn unlift(&self) -> Lit;
}

impl LiftedClauseIdIF for ClauseId {
    /// return `true` if the clause is generated from a literal by Eliminator.
    fn is_lifted(&self) -> bool {
        0 != 0x8000_0000 & NonZeroU32::get(self.ordinal)
    }
    fn lift(l: &Lit) -> Self {
        ClauseId {
            ordinal: NonZeroU32::from(l) | 0x8000_0000,
        }
    }
    fn unlift(&self) -> Lit {
        Lit::from(unsafe { NonZeroU32::new_unchecked(NonZeroU32::get(self.ordinal) & 0x7FFF_FFFF) })
    }
}

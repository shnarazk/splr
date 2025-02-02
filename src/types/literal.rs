use {
    crate::{
        cdb::ClauseId,
        types::var::{Var, VarId},
    },
    std::{
        fmt,
        num::NonZeroU32,
        ops::{Index, IndexMut, Not},
    },
};

/// Literal encoded on `u32` as:
///
/// - the Literal corresponding to a positive occurrence of *variable `n` is `2 * n` and
/// - that for the negative one is `2 * n + 1`.
///
/// # Examples
///
/// ```
/// use splr::types::*;
/// assert_eq!(2usize, Literal::from(-1i32).into());
/// assert_eq!(3usize, Literal::from( 1i32).into());
/// assert_eq!(4usize, Literal::from(-2i32).into());
/// assert_eq!(5usize, Literal::from( 2i32).into());
/// assert_eq!( 1i32, Literal::from( 1i32).into());
/// assert_eq!(-1i32, Literal::from(-1i32).into());
/// assert_eq!( 2i32, Literal::from( 2i32).into());
/// assert_eq!(-2i32, Literal::from(-2i32).into());
/// ```
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Literal {
    /// literal encoded into folded u32
    ordinal: NonZeroU32,
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}L", i32::from(self))
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}L", i32::from(self))
    }
}

/// convert literals to `[i32]` (for debug).
pub fn i32s(v: &[Literal]) -> Vec<i32> {
    v.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
}

impl From<(&Var<'_>, bool)> for Literal {
    #[inline]
    fn from((v, negate): (&Var, bool)) -> Self {
        Literal {
            ordinal: unsafe { NonZeroU32::new_unchecked(((v.id as u32) << 1) + (negate as u32)) },
        }
    }
}
impl From<(VarId, bool)> for Literal {
    #[inline]
    fn from((vi, negate): (VarId, bool)) -> Self {
        Literal {
            ordinal: unsafe { NonZeroU32::new_unchecked(((vi as u32) << 1) + (negate as u32)) },
        }
    }
}

impl From<usize> for Literal {
    #[inline]
    fn from(l: usize) -> Self {
        Literal {
            ordinal: unsafe { NonZeroU32::new_unchecked(l as u32) },
        }
    }
}

impl From<u32> for Literal {
    #[inline]
    fn from(l: u32) -> Self {
        Literal {
            ordinal: unsafe { NonZeroU32::new_unchecked(l) },
        }
    }
}

impl From<i32> for Literal {
    #[inline]
    fn from(x: i32) -> Self {
        Literal {
            ordinal: unsafe {
                NonZeroU32::new_unchecked((if x < 0 { -2 * x } else { 2 * x + 1 }) as u32)
            },
        }
    }
}

impl From<ClauseId> for Literal {
    #[inline]
    fn from(cid: ClauseId) -> Self {
        Literal {
            ordinal: unsafe {
                NonZeroU32::new_unchecked(NonZeroU32::get(cid.ordinal) & 0x7FFF_FFFF)
            },
        }
    }
}

impl From<Literal> for bool {
    /// - negative Literal (= even u32) => Some(false)
    /// - positive Literal (= odd u32)  => Some(true)
    #[inline]
    fn from(l: Literal) -> bool {
        (NonZeroU32::get(l.ordinal) & 1) != 0
    }
}

impl From<Literal> for ClauseId {
    #[inline]
    fn from(l: Literal) -> ClauseId {
        ClauseId {
            ordinal: unsafe { NonZeroU32::new_unchecked(NonZeroU32::get(l.ordinal) | 0x8000_0000) },
        }
    }
}

impl From<Literal> for usize {
    #[inline]
    fn from(l: Literal) -> usize {
        NonZeroU32::get(l.ordinal) as usize
    }
}

impl From<Literal> for i32 {
    #[inline]
    fn from(l: Literal) -> i32 {
        if NonZeroU32::get(l.ordinal) % 2 == 0 {
            -((NonZeroU32::get(l.ordinal) >> 1) as i32)
        } else {
            (NonZeroU32::get(l.ordinal) >> 1) as i32
        }
    }
}

impl From<&Literal> for i32 {
    #[inline]
    fn from(l: &Literal) -> i32 {
        if NonZeroU32::get(l.ordinal) % 2 == 0 {
            -((NonZeroU32::get(l.ordinal) >> 1) as i32)
        } else {
            (NonZeroU32::get(l.ordinal) >> 1) as i32
        }
    }
}

impl Not for Literal {
    type Output = Literal;
    #[inline]
    fn not(self) -> Self {
        Literal {
            ordinal: unsafe { NonZeroU32::new_unchecked(NonZeroU32::get(self.ordinal) ^ 1) },
        }
    }
}

impl Index<Literal> for [bool] {
    type Output = bool;
    #[inline]
    fn index(&self, l: Literal) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self[usize::from(l)]
    }
}

impl IndexMut<Literal> for [bool] {
    #[inline]
    fn index_mut(&mut self, l: Literal) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked_mut(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self[usize::from(l)]
    }
}

impl Index<Literal> for Vec<bool> {
    type Output = bool;
    #[inline]
    fn index(&self, l: Literal) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self[usize::from(l)]
    }
}

impl IndexMut<Literal> for Vec<bool> {
    #[inline]
    fn index_mut(&mut self, l: Literal) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked_mut(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self[usize::from(l)]
    }
}

/// # Examples
///
/// ```
/// use splr::types::*;
/// assert_eq!(Literal::from(1i32), Literal::from((1 as VarId, true)));
/// assert_eq!(Literal::from(2i32), Literal::from((2 as VarId, true)));
/// assert_eq!(1, Literal::from((1usize, true)).vi());
/// assert_eq!(1, Literal::from((1usize, false)).vi());
/// assert_eq!(2, Literal::from((2usize, true)).vi());
/// assert_eq!(2, Literal::from((2usize, false)).vi());
/// assert_eq!(Literal::from( 1i32), !Literal::from(-1i32));
/// assert_eq!(Literal::from(-1i32), !Literal::from( 1i32));
/// assert_eq!(Literal::from( 2i32), !Literal::from(-2i32));
/// assert_eq!(Literal::from(-2i32), !Literal::from( 2i32));
/// ```
impl Literal {
    /// convert to bool.
    #[inline]
    fn as_bool(&self) -> bool {
        NonZeroU32::get(self.ordinal) & 1 == 1
    }
    /// convert to `VarId`.
    #[inline]
    fn vi(self) -> VarId {
        (NonZeroU32::get(self.ordinal) >> 1) as VarId
    }
}

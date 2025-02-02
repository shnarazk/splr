use {
    crate::types::{ClauseId, VarId},
    std::{
        fmt,
        num::NonZeroU32,
        ops::{Index, IndexMut, Not},
    },
};

/// API for Literal like `vi`, `as_bool`, `is_none` and so on.
pub trait LitIF {
    /// convert to bool
    fn as_bool(&self) -> bool;
    /// convert to var index.
    fn vi(self) -> VarId;
}

/// Literal encoded on `u32` as:
///
/// - the literal corresponding to a positive occurrence of *variable `n` is `2 * n` and
/// - that for the negative one is `2 * n + 1`.
///
/// # Examples
///
/// ```
/// use splr::types::*;
/// assert_eq!(2usize, Lit::from(-1i32).into());
/// assert_eq!(3usize, Lit::from( 1i32).into());
/// assert_eq!(4usize, Lit::from(-2i32).into());
/// assert_eq!(5usize, Lit::from( 2i32).into());
/// assert_eq!( 1i32, Lit::from( 1i32).into());
/// assert_eq!(-1i32, Lit::from(-1i32).into());
/// assert_eq!( 2i32, Lit::from( 2i32).into());
/// assert_eq!(-2i32, Lit::from(-2i32).into());
/// ```
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lit {
    /// literal encoded into folded u32
    ordinal: NonZeroU32,
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}L", i32::from(self))
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}L", i32::from(self))
    }
}

/// convert literals to `[i32]` (for debug).
pub fn i32s(v: &[Lit]) -> Vec<i32> {
    v.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
}

impl From<(VarId, bool)> for Lit {
    #[inline]
    fn from((vi, b): (VarId, bool)) -> Self {
        Lit {
            ordinal: unsafe { NonZeroU32::new_unchecked(((vi as u32) << 1) + (b as u32)) },
        }
    }
}

impl From<usize> for Lit {
    #[inline]
    fn from(l: usize) -> Self {
        Lit {
            ordinal: unsafe { NonZeroU32::new_unchecked(l as u32) },
        }
    }
}

impl From<u32> for Lit {
    #[inline]
    fn from(l: u32) -> Self {
        Lit {
            ordinal: unsafe { NonZeroU32::new_unchecked(l) },
        }
    }
}

impl From<i32> for Lit {
    #[inline]
    fn from(x: i32) -> Self {
        Lit {
            ordinal: unsafe {
                NonZeroU32::new_unchecked((if x < 0 { -2 * x } else { 2 * x + 1 }) as u32)
            },
        }
    }
}

impl From<ClauseId> for Lit {
    #[inline]
    fn from(cid: ClauseId) -> Self {
        Lit {
            ordinal: unsafe {
                NonZeroU32::new_unchecked(NonZeroU32::get(cid.ordinal) & 0x7FFF_FFFF)
            },
        }
    }
}

impl From<Lit> for bool {
    /// - positive Lit (= even u32) => Some(true)
    /// - negative Lit (= odd u32)  => Some(false)
    #[inline]
    fn from(l: Lit) -> bool {
        (NonZeroU32::get(l.ordinal) & 1) != 0
    }
}

impl From<Lit> for ClauseId {
    #[inline]
    fn from(l: Lit) -> ClauseId {
        ClauseId {
            ordinal: unsafe { NonZeroU32::new_unchecked(NonZeroU32::get(l.ordinal) | 0x8000_0000) },
        }
    }
}

impl From<Lit> for usize {
    #[inline]
    fn from(l: Lit) -> usize {
        NonZeroU32::get(l.ordinal) as usize
    }
}

impl From<Lit> for i32 {
    #[inline]
    fn from(l: Lit) -> i32 {
        if NonZeroU32::get(l.ordinal) % 2 == 0 {
            -((NonZeroU32::get(l.ordinal) >> 1) as i32)
        } else {
            (NonZeroU32::get(l.ordinal) >> 1) as i32
        }
    }
}

impl From<&Lit> for i32 {
    #[inline]
    fn from(l: &Lit) -> i32 {
        if NonZeroU32::get(l.ordinal) % 2 == 0 {
            -((NonZeroU32::get(l.ordinal) >> 1) as i32)
        } else {
            (NonZeroU32::get(l.ordinal) >> 1) as i32
        }
    }
}

impl Not for Lit {
    type Output = Lit;
    #[inline]
    fn not(self) -> Self {
        Lit {
            ordinal: unsafe { NonZeroU32::new_unchecked(NonZeroU32::get(self.ordinal) ^ 1) },
        }
    }
}

impl Index<Lit> for [bool] {
    type Output = bool;
    #[inline]
    fn index(&self, l: Lit) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self[usize::from(l)]
    }
}

impl IndexMut<Lit> for [bool] {
    #[inline]
    fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked_mut(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self[usize::from(l)]
    }
}

impl Index<Lit> for Vec<bool> {
    type Output = bool;
    #[inline]
    fn index(&self, l: Lit) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self[usize::from(l)]
    }
}

impl IndexMut<Lit> for Vec<bool> {
    #[inline]
    fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
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
/// assert_eq!(Lit::from(1i32), Lit::from((1 as VarId, true)));
/// assert_eq!(Lit::from(2i32), Lit::from((2 as VarId, true)));
/// assert_eq!(1, Lit::from((1usize, true)).vi());
/// assert_eq!(1, Lit::from((1usize, false)).vi());
/// assert_eq!(2, Lit::from((2usize, true)).vi());
/// assert_eq!(2, Lit::from((2usize, false)).vi());
/// assert_eq!(Lit::from( 1i32), !Lit::from(-1i32));
/// assert_eq!(Lit::from(-1i32), !Lit::from( 1i32));
/// assert_eq!(Lit::from( 2i32), !Lit::from(-2i32));
/// assert_eq!(Lit::from(-2i32), !Lit::from( 2i32));
/// ```
impl LitIF for Lit {
    #[inline]
    fn as_bool(&self) -> bool {
        NonZeroU32::get(self.ordinal) & 1 == 1
    }
    #[inline]
    fn vi(self) -> VarId {
        (NonZeroU32::get(self.ordinal) >> 1) as VarId
    }
}

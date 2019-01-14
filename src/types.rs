//! Basic types
use crate::traits::*;
use std::fmt;
use std::ops::Neg;

/// Variable as Index is `usize`
pub type VarId = usize;

/// Clause Identifier. Note: it changes after database reduction.
pub type ClauseId = usize;

/// is a dummy clause index
pub const NULL_CLAUSE: ClauseId = 0;

/// Literal encoded on unsigned integer
/// # Examples
///
/// ```
/// use splr::traits::{LitIF, VarIdIF};
/// use splr::types::*;
/// assert_eq!(2, int2lit( 1) as i32);
/// assert_eq!(3, int2lit(-1) as i32);
/// assert_eq!(4, int2lit( 2) as i32);
/// assert_eq!(5, int2lit(-2) as i32);
/// assert_eq!( 1, int2lit( 1).int());
/// assert_eq!(-1, int2lit(-1).int());
/// assert_eq!( 2, int2lit( 2).int());
/// assert_eq!(-2, int2lit(-2).int());
/// ```
pub type Lit = u32;

/// a dummy literal.
pub const NULL_LIT: Lit = 0;

pub fn int2lit(x: i32) -> Lit {
    (if x < 0 { -2 * x + 1 } else { 2 * x }) as Lit
}

/// # Examples
///
/// ```
/// use splr::traits::{LitIF, VarIdIF};
/// use splr::types::*;
/// assert_eq!(int2lit(1), (1 as VarId).lit(LTRUE));
/// assert_eq!(int2lit(2), (2 as VarId).lit(LTRUE));
/// assert_eq!(1, 1.lit(LTRUE).vi());
/// assert_eq!(1, 1.lit(LFALSE).vi());
/// assert_eq!(2, 2.lit(LTRUE).vi());
/// assert_eq!(2, 2.lit(LFALSE).vi());
/// assert_eq!(int2lit( 1), int2lit(-1).negate());
/// assert_eq!(int2lit(-1), int2lit( 1).negate());
/// assert_eq!(int2lit( 2), int2lit(-2).negate());
/// assert_eq!(int2lit(-2), int2lit( 2).negate());
/// ```

impl LitIF for Lit {
    #[inline(always)]
    fn vi(&self) -> VarId {
        (self >> 1) as VarId
    }
    fn int(&self) -> i32 {
        if self % 2 == 0 {
            (*self >> 1) as i32
        } else {
            ((*self >> 1) as i32).neg()
        }
    }
    /// - positive Lit (= even u32) => LTRUE (= 1 as u8)
    /// - negative Lit (= odd u32)  => LFASE (= 0 as u8)
    #[inline(always)]
    fn lbool(&self) -> Lbool {
        (self & 1 == 0) as Lbool
    }
    #[inline(always)]
    fn positive(&self) -> bool {
        self & 1 == 0
    }
    #[inline(always)]
    fn negate(&self) -> Lit {
        self ^ 1
    }
    fn to_cid(self) -> ClauseId {
        (self as usize) | 0x8000_0000_0000_0000
    }
}

impl VarIdIF for VarId {
    /// converter from [VarId](type.VarId.html) to [Lit](type.Lit.html).
    /// returns a positive literal if p == LTRUE or BOTTOM.
    #[inline(always)]
    fn lit(&self, p: Lbool) -> Lit {
        (*self as Lit) << 1 | ((p == LFALSE) as Lit)
    }
}

/// Lifted Bool type
pub type Lbool = u8;
/// the lifted **false**.
pub const LFALSE: u8 = 0;
/// the lifted **true**.
pub const LTRUE: u8 = 1;
/// unbound bool.
pub const BOTTOM: u8 = 2;

/// Note: this function doesn't work on BOTTOM.
pub fn negate_bool(b: Lbool) -> Lbool {
    b ^ 1
}

/// data about a problem.
pub struct CNFDescription {
    pub num_of_variables: usize,
    pub num_of_clauses: usize,
    pub pathname: String,
}

impl fmt::Display for CNFDescription {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let CNFDescription {
            num_of_variables: nv,
            num_of_clauses: nc,
            pathname: path,
        } = &self;
        write!(f, "CNF({}, {}, {})", nv, nc, path)
    }
}

pub fn vec2int(v: &[Lit]) -> Vec<i32> {
    v.iter()
        .map(|l| match l {
            0 => 0,
            1 => 0,
            x => x.int(),
        })
        .collect::<Vec<i32>>()
}

impl<T> Delete<T> for Vec<T> {
    fn delete_stable<F>(&mut self, mut filter: F)
    where
        F: FnMut(&T) -> bool,
    {
        let mut i = 0;
        while i != self.len() {
            if filter(&mut self[i]) {
                self.remove(i);
                break;
            } else {
                i += 1;
            }
        }
    }
    #[inline(always)]
    fn delete_unstable<F>(&mut self, mut filter: F)
    where
        F: FnMut(&T) -> bool,
    {
        let mut i = 0;
        while i != self.len() {
            if filter(&mut self[i]) {
                self.swap_remove(i);
                break;
            } else {
                i += 1;
            }
        }
    }
}

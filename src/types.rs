//! Basic types
use crate::traits::{Delete, LitIF};
use std::fmt;
use std::ops::Neg;

/// 'Variable' identifier or 'variable' index, starting with one.
pub type VarId = usize;

/// 'Clause' Identifier, or 'clause' index, starting with one.
/// Note: ids are re-used after 'garbage collection'.
pub type ClauseId = u32;

/// a dummy clause index.
pub const NULL_CLAUSE: ClauseId = 0;

/// Literal encoded on `u32` as:
///
/// - the literal corresponding to a positive occurrence of *variable `n` is `2 * n` and
/// - that for the negative one is `2 * n + 1`.
///
/// # Examples
///
/// ```
/// use splr::traits::LitIF;
/// use splr::types::*;
/// assert_eq!(2, Lit::from_int( 1) as i32);
/// assert_eq!(3, Lit::from_int(-1) as i32);
/// assert_eq!(4, Lit::from_int( 2) as i32);
/// assert_eq!(5, Lit::from_int(-2) as i32);
/// assert_eq!( 1, Lit::from_int( 1).to_i32());
/// assert_eq!(-1, Lit::from_int(-1).to_i32());
/// assert_eq!( 2, Lit::from_int( 2).to_i32());
/// assert_eq!(-2, Lit::from_int(-2).to_i32());
/// ```
pub type Lit = u32;

/// a dummy literal.
pub const NULL_LIT: Lit = 0;

/// # Examples
///
/// ```
/// use splr::traits::LitIF;
/// use splr::types::*;
/// assert_eq!(Lit::from_int(1), Lit::from_var(1 as VarId, TRUE));
/// assert_eq!(Lit::from_int(2), Lit::from_var(2 as VarId, TRUE));
/// assert_eq!(1, Lit::from_var(1, TRUE).vi());
/// assert_eq!(1, Lit::from_var(1, FALSE).vi());
/// assert_eq!(2, Lit::from_var(2, TRUE).vi());
/// assert_eq!(2, Lit::from_var(2, FALSE).vi());
/// assert_eq!(Lit::from_int( 1), Lit::from_int(-1).negate());
/// assert_eq!(Lit::from_int(-1), Lit::from_int( 1).negate());
/// assert_eq!(Lit::from_int( 2), Lit::from_int(-2).negate());
/// assert_eq!(Lit::from_int(-2), Lit::from_int( 2).negate());
/// ```

impl LitIF for Lit {
    fn from_int(x: i32) -> Lit {
        (if x < 0 { -2 * x + 1 } else { 2 * x }) as Lit
    }
    fn from_var(vi: VarId, p: Lbool) -> Lit {
        (vi as Lit) << 1 | ((p == FALSE) as Lit)
    }
    fn vi(self) -> VarId {
        (self >> 1) as VarId
    }
    fn to_i32(self) -> i32 {
        if self % 2 == 0 {
            (self >> 1) as i32
        } else {
            ((self >> 1) as i32).neg()
        }
    }
    /// - positive Lit (= even u32) => TRUE (= 1 as u8)
    /// - negative Lit (= odd u32)  => LFASE (= 0 as u8)
    fn lbool(self) -> Lbool {
        (self & 1 == 0) as Lbool
    }
    fn is_positive(self) -> bool {
        self & 1 == 0
    }
    fn negate(self) -> Lit {
        self ^ 1
    }
    fn to_cid(self) -> ClauseId {
        (self as ClauseId) | 0x8000_0000
    }
}

/// Lifted Bool type, consisting of
///  - `FALSE`
///  - `TRUE`
///  - `BOTTOM`
pub type Lbool = u8;
/// the lifted **false**.
pub const FALSE: u8 = 0;
/// the lifted **true**.
pub const TRUE: u8 = 1;
/// unbound bool.
pub const BOTTOM: u8 = 2;

/// Note: this function doesn't work on BOTTOM.
#[allow(dead_code)]
fn negate_bool(b: Lbool) -> Lbool {
    b ^ 1
}

/// Internal exception
// Returning `Result<(), a-singleton>` is identical to returning `bool`.
pub enum SolverError {
    Inconsistent,
}

/// A Return type used by solver functions
pub type MaybeInconsistent = Result<(), SolverError>;

/// data about a problem.
#[derive(Clone, Debug)]
pub struct CNFDescription {
    pub num_of_variables: usize,
    pub num_of_clauses: usize,
    pub pathname: String,
}

impl Default for CNFDescription {
    fn default() -> CNFDescription {
        CNFDescription {
            num_of_variables: 0,
            num_of_clauses: 0,
            pathname: "".to_string(),
        }
    }
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

/// convert `[Lit]` to `[i32]` (for debug)
pub fn vec2int(v: &[Lit]) -> Vec<i32> {
    v.iter()
        .map(|l| match l {
            0 => 0,
            1 => 0,
            x => x.to_i32(),
        })
        .collect::<Vec<i32>>()
}

impl<T> Delete<T> for Vec<T> {
    fn delete_unstable<F>(&mut self, mut filter: F)
    where
        F: FnMut(&T) -> bool,
    {
        let mut i = 0;
        while i != self.len() {
            if filter(&mut self[i]) {
                self.swap_remove(i); // self.remove(i) for stable deletion
                break;
            } else {
                i += 1;
            }
        }
    }
}

bitflags! {
    pub struct Flag: u16 {
        /// a clause is stored in DB, but is a garbage now.
        const DEAD         = 0b0000_0000_0000_0001;
        /// a clause is a generated clause by conflict analysis and is removable.
        const LEARNT       = 0b0000_0000_0000_0010;
        /// a clause is used recently in conflict analysis.
        const JUST_USED    = 0b0000_0000_0000_0100;
        /// a clause is registered in vars' occurrence list.
        const OCCUR_LINKED = 0b0000_0000_0000_1000;
        /// a clause or var is enqueued for eliminator.
        const ENQUEUED     = 0b0000_0000_0001_0000;
        /// a var is eliminated and managed by eliminator.
        const ELIMINATED   = 0b0000_0000_0010_0000;
        /// mark to run garbage collector on the corresponding watcher lists
        const TOUCHED      = 0b0000_0000_0100_0000;
        /// a variable is used as a first UID in the present run
        const FUP          = 0b0000_0000_1000_0000;
        const CNFVAR       = 0b0000_0001_0000_0000;
        const CNFLIT       = 0b0000_0010_0000_0000;
        const LAST_CNF     = 0b0000_0100_0000_0000;
        const FUL          = 0b0000_1000_0000_0000;
        const LAST_FUL     = 0b0001_0000_0000_0000;
//        /// superium of fup: a variable has ever been used as a first UID so far
//        const SUF          = 0b0000_0001_0000_0000;
//        /// assigned or cancelled variable
//        const ACV          = 0b0000_0010_0000_0000;
//        /// superium of asg: a variable has ever been assigned so far
//        const SUA          = 0b0000_0100_0000_0000;
    }
}

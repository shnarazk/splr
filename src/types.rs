//! Basic types
use crate::traits::{Delete, EmaIF, LitIF};
use std::fmt;
use std::ops::{Index, IndexMut, Neg, Range, RangeFrom};

/// 'Variable' identifier or 'variable' index, starting with one.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VarId {
    ix: usize
}

impl fmt::Display for VarId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "VarID:{}", self.ix)
    }
}

impl From<VarId> for usize {
    fn from(vi: VarId) -> Self { vi.ix }
}

impl From<usize> for VarId {
    fn from(ix: usize) -> Self { VarId { ix } }
}

impl From<VarId> for i32 {
    fn from(vi: VarId) -> Self { vi.ix  as i32 }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct VarIdIndexed<T>
    where T: Sized
{
    pub vec: Vec<T>
}

impl<T> VarIdIndexed<T> {
    pub fn len(&self) -> usize {
        self.vec.len()
    }
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }
    pub fn new() -> Self {
        VarIdIndexed { vec: Vec::new() }
    }
    pub fn push(&mut self, x: T) {
        self.vec.push(x);
    }
    pub fn swap(&mut self, x: VarId, y: VarId) {
        self.vec.swap(usize::from(x), usize::from(y));
    }
}

impl<T> From<Vec<T>> for VarIdIndexed<T> {
    fn from(vec: Vec<T>) -> Self {
        VarIdIndexed {
            vec
        }
    }
}

impl<T> Index<VarId> for VarIdIndexed<T> {
    type Output = T;
    #[inline]
    fn index(&self, vi: VarId) -> &Self::Output {
        unsafe { self.vec.get_unchecked(vi.ix) }
    }
}

impl<T> IndexMut<VarId> for VarIdIndexed<T> {
    #[inline]
    fn index_mut(&mut self, vi: VarId) -> &mut T {
        unsafe { self.vec.get_unchecked_mut(vi.ix) }
    }
}

impl<T> Index<Range<usize>> for VarIdIndexed<T> {
    type Output = [T];
    #[inline]
    fn index(&self, r: Range<usize>) -> &Self::Output {
        &self.vec[r]
    }
}

impl<T> Index<RangeFrom<usize>> for VarIdIndexed<T> {
    type Output = [T];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &Self::Output {
        unsafe { self.vec.get_unchecked(r) }
    }
}

impl<T> IndexMut<Range<usize>> for VarIdIndexed<T> {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut Self::Output {
        unsafe { self.vec.get_unchecked_mut(r) }
    }
}

impl<T> IndexMut<RangeFrom<usize>> for VarIdIndexed<T> {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut Self::Output {
        &mut self.vec[r]
    }
}

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
/// assert_eq!(2, Lit::from_int(-1) as i32);
/// assert_eq!(3, Lit::from_int( 1) as i32);
/// assert_eq!(4, Lit::from_int(-2) as i32);
/// assert_eq!(5, Lit::from_int( 2) as i32);
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
/// assert_eq!(Lit::from_int(1), Lit::from_var(1 as VarId, true));
/// assert_eq!(Lit::from_int(2), Lit::from_var(2 as VarId, true));
/// assert_eq!(1, Lit::from_var(1, true).vi());
/// assert_eq!(1, Lit::from_var(1, false).vi());
/// assert_eq!(2, Lit::from_var(2, true).vi());
/// assert_eq!(2, Lit::from_var(2, false).vi());
/// assert_eq!(Lit::from_int( 1), Lit::from_int(-1).negate());
/// assert_eq!(Lit::from_int(-1), Lit::from_int( 1).negate());
/// assert_eq!(Lit::from_int( 2), Lit::from_int(-2).negate());
/// assert_eq!(Lit::from_int(-2), Lit::from_int( 2).negate());
/// ```

impl LitIF for Lit {
    fn from_int(x: i32) -> Lit {
        (if x < 0 { -2 * x } else { 2 * x + 1 }) as Lit
    }
    fn from_var(vi: VarId, p: bool) -> Lit {
        (vi.ix as Lit) << 1 | (p as Lit)
    }
    fn vi(self) -> VarId {
        VarId { ix: (self >> 1) as usize }
    }
    fn to_i32(self) -> i32 {
        if self % 2 == 0 {
            ((self >> 1) as i32).neg()
        } else {
            (self >> 1) as i32
        }
    }
    /// - positive Lit (= even u32) => Some(true)
    /// - negative Lit (= odd u32)  => Some(false)
    fn as_bool(self) -> bool {
        (self & 1) != 0
    }
    fn negate(self) -> Lit {
        self ^ 1
    }
    fn to_cid(self) -> ClauseId {
        (self as ClauseId) | 0x8000_0000
    }
}

/// Exponential Moving Average w/ a calibrator
#[derive(Debug)]
pub struct Ema {
    val: f64,
    cal: f64,
    sca: f64,
}

impl EmaIF for Ema {
    fn new(s: usize) -> Ema {
        Ema {
            val: 0.0,
            cal: 0.0,
            sca: 1.0 / (s as f64),
        }
    }
    fn update(&mut self, x: f64) {
        self.val = self.sca * x + (1.0 - self.sca) * self.val;
        self.cal = self.sca + (1.0 - self.sca) * self.cal;
    }
    fn get(&self) -> f64 {
        self.val / self.cal
    }
}

/// Exponential Moving Average pair
struct Ema2 {
    fast: f64,
    slow: f64,
    calf: f64,
    cals: f64,
    fe: f64,
    se: f64,
}

impl EmaIF for Ema2 {
    fn new(f: usize) -> Ema2 {
        Ema2 {
            fast: 0.0,
            slow: 0.0,
            calf: 0.0,
            cals: 0.0,
            fe: 1.0 / (f as f64),
            se: 1.0 / (f as f64),
        }
    }
    fn get(&self) -> f64 {
        self.fast / self.calf
    }
    fn update(&mut self, x: f64) {
        self.fast = self.fe * x + (1.0 - self.fe) * self.fast;
        self.slow = self.se * x + (1.0 - self.se) * self.slow;
        self.calf = self.fe + (1.0 - self.fe) * self.calf;
        self.cals = self.se + (1.0 - self.se) * self.cals;
    }
    fn reset(&mut self) {
        self.slow = self.fast;
        self.cals = self.calf;
    }
}

impl Ema2 {
    #[allow(dead_code)]
    fn rate(&self) -> f64 {
        self.fast / self.slow * (self.cals / self.calf)
    }
    #[allow(dead_code)]
    fn with_slow(mut self, s: u64) -> Ema2 {
        self.se = 1.0 / (s as f64);
        self
    }
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
    }
}

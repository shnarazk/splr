//! Basic types
use std::fmt;

/// Variable as Index is `usize`
pub type VarIndex = usize;

/// Clause Index, not ID because it changes after database reduction.
pub type ClauseIndex = usize;

/// is a dummy clause index
pub const NULL_CLAUSE: ClauseIndex = 0;

/// Literal encoded on unsigned integer
/// # Examples
///
/// ```
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
    (if x < 0 { -2 * x + 1 } else { 2 * x }) as u32
}

/// Converters between 'int', [Lit](type.Lit.html) and [Var](type.Var.html).
/// # Examples
///
/// ```
/// use splr::types::*;
/// assert_eq!(int2lit(1), 1.lit(LTRUE));
/// assert_eq!(int2lit(2), 2.lit(LTRUE));
/// assert_eq!(1, 1.lit(LTRUE).vi());
/// assert_eq!(1, 1.lit(LFALSE).vi());
/// assert_eq!(2, 2.lit(LTRUE).vi());
/// assert_eq!(2, 2.lit(LFALSE).vi());
/// assert_eq!(int2lit( 1), int2lit(-1).negate());
/// assert_eq!(int2lit(-1), int2lit( 1).negate());
/// assert_eq!(int2lit( 2), int2lit(-2).negate());
/// assert_eq!(int2lit(-2), int2lit( 2).negate());
/// ```
pub trait LiteralEncoding {
    fn vi(&self) -> VarIndex;
    fn int(&self) -> i32;
    fn lbool(&self) -> Lbool;
    fn positive(&self) -> bool;
    fn negate(&self) -> Lit;
}

impl LiteralEncoding for Lit {
    fn vi(&self) -> VarIndex {
        (self / 2) as VarIndex
    }
    fn int(&self) -> i32 {
        if self % 2 == 0 {
            (*self / 2) as i32
        } else {
            (*self as i32) / -2
        }
    }
    fn lbool(&self) -> Lbool {
        if self.positive() {
            LTRUE
        } else {
            LFALSE
        }
    }
    fn positive(&self) -> bool {
        self % 2 == 0
    }
    fn negate(&self) -> Lit {
        self ^ 1
    }
}

/// converter from [VarIndex](type.VarIndex.html) to [Lit](type.Lit.html).
pub trait VarIndexEncoding {
    fn lit(&self, p: Lbool) -> Lit;
}

impl VarIndexEncoding for VarIndex {
    fn lit(&self, p: Lbool) -> Lit {
        (if p == LFALSE { 2 * self + 1 } else { 2 * self }) as Lit
    }
}

/// Lifted Bool type
pub type Lbool = i8;
/// the lifted **true**.
pub const LTRUE: i8 = 1;
/// the lifted **false**.
pub const LFALSE: i8 = -1;
/// unbound bool.
pub const BOTTOM: i8 = 0;

pub fn negate_bool(b: Lbool) -> Lbool {
    match b {
        LTRUE => LFALSE,
        LFALSE => LTRUE,
        _ => BOTTOM,
    }
}

/// trait on Ema
pub trait EmaKind {
    /// returns a new EMA from a flag (slow or fast) and a window size
    fn get(&self) -> f64;
    /// returns an EMA value
    fn update(&mut self, x: f64) -> f64;
}

/// Exponential Moving Average with a calibrator
#[derive(Debug)]
pub struct Ema2 {
    pub fast: f64,
    pub slow: f64,
    fe: f64,
    se: f64,
}

impl Ema2 {
    pub fn new(f: i32, s: i32) -> Ema2 {
        Ema2 {
            fast: 0.0,
            slow: 0.0,
            fe: 1.0 / f as f64,
            se: 1.0 / s as f64,
        }
    }
}

impl EmaKind for Ema2 {
    fn get(&self) -> f64 {
        self.fast / self.slow
    }
    fn update(&mut self, x: f64) -> f64 {
        self.fast = &self.fe * x + (1.0 - &self.fe) * &self.fast;
        self.slow = &self.se * x + (1.0 - &self.se) * &self.slow;
        self.fast / self.slow
    }
}

/// In splr, the watch map is reseted at the beginning of every simplification phase.
/// It's just a immutable index (with some data) referring to a Clause in a Vec.
#[derive(Debug, PartialEq)]
pub struct Watch {
    pub other: Lit,
    pub by: ClauseIndex,
    pub to: Lit,
    pub swap: usize,
}

impl Watch {
    pub fn new(o: Lit, b: ClauseIndex) -> Watch {
        Watch {
            other: o,
            by: b,
            to: NULL_LIT,
            swap: 0,
        }
    }
}

/// is a mapping from `Lit` to `Vec<Watch>`.
pub type WatchMap = Vec<Vec<Watch>>;

/// returns `WatchMap`, or `Vec<Vec<Watch>>`.
pub fn new_watch_map(nv: usize) -> WatchMap {
    let size = 2 * (nv + 1);
    let mut vec = Vec::with_capacity(size);
    for _i in 0..size {
        vec.push(Vec::with_capacity(40));
    }
    vec
}

pub fn set_watch(w: &mut [Vec<Watch>], ci: ClauseIndex, w0: Lit, w1: Lit) -> () {
    debug_assert_ne!(ci, NULL_CLAUSE);
    w[w0.negate() as usize].push(Watch::new(w1, ci));
    w[w1.negate() as usize].push(Watch::new(w0, ci));
}

#[derive(Debug)]
pub struct Ema(f64, f64, f64);

impl Ema {
    pub fn new(s: i32) -> Ema {
        Ema(0.0, 1.0 / s as f64, 0.0)
    }
}

impl EmaKind for Ema {
    fn get(&self) -> f64 {
        self.0 / self.2
    }
    fn update(&mut self, x: f64) -> f64 {
        let e = &self.1 * x + (1.0 - &self.1) * &self.0;
        self.0 = e;
        let c = &self.1 + (1.0 - &self.1) * &self.2;
        self.2 = c;
        e / c
    }
}

/// Exponential Moving Average w/o a calibrator
#[derive(Debug)]
pub struct Ema_(f64, f64);

impl Ema_ {
    pub fn new(s: i32) -> Ema_ {
        Ema_(0.0, 1.0 / s as f64)
    }
}

impl EmaKind for Ema_ {
    fn get(&self) -> f64 {
        self.0 / self.1
    }
    fn update(&mut self, x: f64) -> f64 {
        let e = &self.1 * x + (1.0 - &self.1) * &self.0;
        self.0 = e;
        e
    }
}

/// data about a problem.
#[derive(Debug)]
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

#[derive(Debug)]
/// `Solver`'s parameters; random decision rate was dropped.
pub struct SolverConfiguration {
    /// decay rate for variable activity
    pub variable_decay_rate: f64,
    /// decay rate for clause activity
    pub clause_decay_rate: f64,
    /// dump stats data during solving
    pub dump_solver_stat_mode: i32,
    /// the coefficients for restarts
    pub ema_coeffs: (i32, i32),
    /// restart expansion factor
    pub restart_expansion: f64,
    /// static steps between restarts
    pub restart_step: f64,
}

impl Default for SolverConfiguration {
    fn default() -> SolverConfiguration {
        SolverConfiguration {
            variable_decay_rate: 0.95,
            clause_decay_rate: 0.999,
            dump_solver_stat_mode: 0,
            ema_coeffs: (2 ^ 5, 2 ^ 14),
            restart_expansion: 1.15,
            restart_step: 100.0,
        }
    }
}

/// formats of state dump
pub enum DumpMode {
    NoDump = 0,
    DumpCSVHeader,
    DumpCSV,
    DumpJSON,
}

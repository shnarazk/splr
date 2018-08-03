//! Basic types
use std::fmt;

/// Literal encoded on unsigned integer
/// # Examples
///
/// ```
/// use splr::types::*;
/// assert_eq!(2, int2lit( 1) as i64);
/// assert_eq!(3, int2lit(-1) as i64);
/// assert_eq!(4, int2lit( 2) as i64);
/// assert_eq!(5, int2lit(-2) as i64);
/// assert_eq!( 1, lit2int(int2lit( 1)));
/// assert_eq!(-1, lit2int(int2lit(-1)));
/// assert_eq!( 2, lit2int(int2lit( 2)));
/// assert_eq!(-2, lit2int(int2lit(-2)));
/// ```
pub type Lit = u32;

pub fn int2lit(x: i64) -> Lit {
    (if x < 0 { -2 * x + 1 } else { 2 * x }) as u32
}
pub fn lit2int(x: Lit) -> i64 {
    if x % 2 == 0 {
        x as i64 / 2
    } else {
        (x as i64) / -2
    }
}

/// Variable encoded on unsigned integer
/// # Examples
///
/// ```
/// use splr::types::*;
/// assert_eq!(1, int2var(1) as i64);
/// assert_eq!(2, int2var(2) as i64);
/// assert_eq!( 1, var2int(int2var(1)));
/// assert_eq!( 2, var2int(int2var(2)));
/// ```
pub type Var = u32;

pub fn int2var(x: i64) -> Var {
    x as Var
}
pub fn var2int(x: Var) -> i64 {
    x as i64
}

/// Converters
/// # Examples
///
/// ```
/// use splr::types::*;
/// assert_eq!(int2lit(1), var2lit(1));
/// assert_eq!(int2lit(2), var2lit(2));
/// assert_eq!(int2var(1), lit2var(int2lit( 1)));
/// assert_eq!(int2var(1), lit2var(int2lit(-1)));
/// assert_eq!(int2var(2), lit2var(int2lit( 2)));
/// assert_eq!(int2var(2), lit2var(int2lit(-2)));
/// ```
pub fn lit2var(x: Lit) -> Var {
    (x / 2) as Var
}
pub fn var2lit(x: Var) -> Lit {
    (2 * x) as Lit
}

/// Lifted Bool
pub const LTRUE: i32 = 1;
pub const LFALSE: i32 = -1;
pub const BOTTOM: i32 = 0;

/// trait on Ema
pub trait EmaKind {
    /// returns a new EMA from a flag (slow or fast) and a window size
    fn get(&self) -> f64;
    /// returns an EMA value
    fn update(&mut self, x: f64) -> f64;
}

/// Exponential Moving Average, EMA with a calibrator
pub struct Ema(f64, f64, f64);

impl Ema {
    pub fn new(s: i64) -> Ema {
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

// Exponential Moving Average, EMA w/o a calibrator
pub struct Ema_(f64, f64);

impl Ema_ {
    pub fn new(s: i64) -> Ema_ {
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

#[derive(Debug)]
pub struct CNFDescription {
    num_of_variables: u32,
    num_of_clauses: u64,
    pathname: String,
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
    variable_decay_rate: f64,
    /// decay rate for clause activity
    clause_decay_rate: f64,
    /// dump stats data during solving
    dump_solver_stat_mode: i64,
    /// the coefficients for restarts
    ema_coeffs: (i64, i64),
    /// restart expansion factor
    restart_expansion: f64,
    /// static steps between restarts
    restart_step: f64,
}

pub const DEFAULT_CONFIGURATION: SolverConfiguration = SolverConfiguration {
    variable_decay_rate: 0.95,
    clause_decay_rate: 0.999,
    dump_solver_stat_mode: 0,
    ema_coeffs: (2 ^ 5, 2 ^ 14),
    restart_expansion: 1.15,
    restart_step: 100.0,
};

/// stat index
pub enum StatIndex {
    NumOfBackjump,     // the number of backjump
    NumOfRestart,      // the number of restart
    NumOfBlockRestart, // the number of blacking start
    NumOfPropagation,  // the number of propagation
    NumOfReduction,    // the number of reduction
    NumOfClause,       // the number of 'alive' given clauses
    NumOfLearnt,       // the number of 'alive' learnt clauses
    NumOfVariable,     // the number of 'alive' variables
    NumOfAssigned,     // the number of assigned variables
    EndOfStatIndex,    // Don't use this dummy.
}

/// formats of state dump
pub enum DumpMode {
    NoDump,
    DumpCSVHeader,
    DumpCSV,
    DumpJSON,
}

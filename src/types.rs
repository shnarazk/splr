#![allow(dead_code)]
#![allow(unused_imports)]

//! Basic types
use std::fmt;

/// normal results returned by Solver
pub enum Certificate {
    SAT(Vec<i32>),
    UNSAT(Vec<i32>), // FIXME: replace with DRAT
}

/// abnormal termination flags
pub enum SolverException {
    StateUNSAT,           // 0
    StateSAT,             // 1
    OutOfMemory,          // 2
    TimeOut,              // 3
    InternalInconsistent, // 4
    UndescribedError,     // 5
}

/// The type that `Solver` returns
/// This captures the following three cases:
/// * solved with a satisfiable assigment,
/// * proved that it's an unsatisfiable problem, and
/// * aborted due to Mios specification or an internal error
type SolverResult = Result<Certificate, SolverException>;

/// Literal encoded on unsigned integer
/// # Examples
///
/// ```
/// use splr::types::*;
/// assert_eq!(2, int2lit( 1) as i32);
/// assert_eq!(3, int2lit(-1) as i32);
/// assert_eq!(4, int2lit( 2) as i32);
/// assert_eq!(5, int2lit(-2) as i32);
/// assert_eq!( 1, lit2int(int2lit( 1)));
/// assert_eq!(-1, lit2int(int2lit(-1)));
/// assert_eq!( 2, lit2int(int2lit( 2)));
/// assert_eq!(-2, lit2int(int2lit(-2)));
/// ```
pub type Lit = u32;

pub fn int2lit(x: i32) -> Lit {
    (if x < 0 { -2 * x + 1 } else { 2 * x }) as u32
}
pub fn lit2int(x: Lit) -> i32 {
    if x % 2 == 0 {
        x as i32 / 2
    } else {
        (x as i32) / -2
    }
}

pub fn positive_lit(l: Lit) -> bool {
    l % 2 == 0
}

/// ```
/// asert_eq!(int2lit( 1), negate_lit(int2lit(-1)));
/// asert_eq!(int2lit(-1), negate_lit(int2lit( 1)));
/// asert_eq!(int2lit( 2), negate_lit(int2lit(-2)));
/// asert_eq!(int2lit(-2), negate_lit(int2lit( 2)));
/// ```
pub fn negate_lit(l: Lit) -> Lit {
    l ^ 1
}

/// Variable encoded on unsigned integer
/// # Examples
///
/// ```
/// use splr::types::*;
/// assert_eq!(1, int2var(1) as i32);
/// assert_eq!(2, int2var(2) as i32);
/// assert_eq!( 1, var2int(int2var(1)));
/// assert_eq!( 2, var2int(int2var(2)));
/// ```
pub type Var = u32;

pub fn int2var(x: i32) -> Var {
    x as Var
}
pub fn var2int(x: Var) -> i32 {
    x as i32
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
pub type LBool = i8;
pub const LTRUE: i8 = 1;
pub const LFALSE: i8 = -1;
pub const BOTTOM: i8 = 0;

pub fn negate_bool(b: LBool) -> LBool {
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

/// Exponential Moving Average, EMA with a calibrator
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

// Exponential Moving Average, EMA w/o a calibrator
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

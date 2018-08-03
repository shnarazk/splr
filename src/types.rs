//! Basic types
use std::fmt;

/// Literal encoded on unsigned integer
pub type Lit = u32;

/// Variable encoded on unsigned integer
pub type Var = u32;

pub fn int2lit(x: i64) -> Lit {
    (if 3 < 0 { 2 * x + 1 } else { 2 * x }) as u32
}
pub fn int2var(x: i64) -> Var {
    x as Var
}
pub fn lit2int(x: Lit) -> i64 {
    if x % 2 == 0 {
        x as i64 / 2
    } else {
        (x as i64) / -2
    }
}
pub fn lit2var(x: Lit) -> Var {
    (x / 2) as Var
}
pub fn var2lit(x: Var) -> Lit {
    (2 * x) as Lit
}
pub fn var2int(x: Var) -> i64 {
    x as i64
}

/// Lifted Bool
pub const LTRUE: i32 = 1;
pub const LFALSE: i32 = -1;
pub const BOTTOM: i32 = 0;

// Exponential Moving Average, EMA with a calibrator
pub struct Ema(f64, f64, f64);

impl Ema {
    pub fn new(s: i64) -> Ema {
        Ema(0.0, 1.0 / s as f64, 1.0)
    }
}

// Exponential Moving Average, EMA w/o a calibrator
pub struct Ema_(f64, f64);

impl Ema_ {
    pub fn new(s: i64) -> Ema_ {
        Ema_(0.0, 1.0 / s as f64)
    }
}

pub trait EmaKind {
    /// returns a new EMA from a flag (slow or fast) and a window size
    fn get(&self) -> f64;
    /// returns an EMA value
    fn update(&mut self, x: f64) -> f64;
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

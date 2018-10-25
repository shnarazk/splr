//! This is a SAT solver in Rust.
#[macro_use]
mod macros;
// /// Subsumption-based clause/var eliminaiton
/// Clause
pub mod clause;
pub mod eliminator;
/// for progress report
pub mod profiler;
/// Implementation on solver restart.
pub mod restart;
/// struct Solver
pub mod solver;
/// Plumping layer.
pub mod types;
/// validates
pub mod validator;
/// Var
pub mod var;

//! This is a SAT solver in Rust.

// /// Subsumption-based clause/var eliminaiton
/// Assignment management
pub mod assign;
/// Clause
pub mod clause;
/// Configuration
pub mod config;
/// In-process elimination
pub mod eliminator;
/// Implementation on solver restart.
pub mod restart;
/// struct Solver
pub mod solver;
/// various data for SAT solving
pub mod state;
/// Traits
pub mod traits;
/// Plumping layer.
pub mod types;
/// validates
pub mod validator;
/// Var
pub mod var;

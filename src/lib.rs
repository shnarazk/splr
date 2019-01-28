//! This is a SAT solver in Rust.

// /// Subsumption-based clause/var eliminaiton
/// Assignment management
pub mod assign;
/// Clause struct
pub mod clause;
/// Solver configuration
pub mod config;
/// Pre/In-processor for clause subsumption and variable elimination
pub mod eliminator;
/// Solver restart implementation
pub mod restart;
/// The main struct
pub mod solver;
/// Collection of various stat data for SAT solving process
pub mod state;
/// Interfaces between submodules (version 0.1)
pub mod traits;
/// Plumping layer
pub mod types;
/// validates a given assignment for a problem.
pub mod validator;
/// Var struct
pub mod var;

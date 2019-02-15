//! This is a SAT solver in Rust.

// /// Subsumption-based clause/var eliminaiton
/// Clause structure
pub mod clause;
/// Parameters used for Solver initialization
pub mod config;
/// Pre/In-processor for clause subsumption and variable elimination
pub mod eliminator;
/// Assignment management
pub mod propagator;
/// Solver restart implementation
pub mod restart;
/// The main structure
pub mod solver;
/// Collection of various data and parameters for SAT solving process
pub mod state;
/// Interfaces between submodules
pub mod traits;
/// Plumping layer
pub mod types;
/// validates a given assignment for a problem.
pub mod validator;
/// Var structure
pub mod var;

//! This is a SAT solver in Rust.

/// Conflict analzyer.
pub mod analyze;
/// Clause
pub mod clause;
/// Implementation on clause elimination.
pub mod clause_select;
/// Implementation on Main algorithm.
pub mod propagate;
/// Implementation on solver restart.
pub mod restart;
/// struct Solver
pub mod solver;
/// Plumping layer.
pub mod types;
/// Var
pub mod var;
/// Implementation on decision var selection.
pub mod var_select;
/// Watch literal structure.
pub mod watch;

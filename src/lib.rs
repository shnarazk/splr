//! This is a SAT solver in Rust.

/// Clause
pub mod clause;
/// Implementation on clause elimination.
pub mod clause_select;
/// Implementation on Main algorithm.
pub mod search;
/// Implementation on solver restart.
pub mod search_restart;
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

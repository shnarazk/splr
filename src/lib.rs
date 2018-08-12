//! This is a SAT solver in Rust.

/// Var and Clause
pub mod clause;
/// Heuristics on clause elimination and restart.
pub mod criteria;
/// Heuristics on solver restart.
pub mod restart;
/// Main algorithm.
pub mod search;
/// struct Solver
pub mod solver;
/// Plumping layer.
pub mod types;

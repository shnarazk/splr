//! This is a SAT solver in Rust.

/// Clause
pub mod clause;
/// Implementation on clause elimination.
pub mod clause_manage;
/// struct Solver
pub mod solver;
/// Conflict analzyer.
pub mod solver_analyze;
/// Implementation on Main algorithm.
pub mod solver_propagate;
/// Implementation on solver restart.
pub mod solver_rollback;
/// Plumping layer.
pub mod types;
/// Var
pub mod var;
/// Implementation on decision var selection.
pub mod var_select;
/// Watch literal structure.
pub mod watch;

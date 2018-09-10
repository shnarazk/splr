//! This is a SAT solver in Rust.
#[macro_use]
mod macros;
/// Assigment
pub mod assign;
/// Clause
pub mod clause;
/// Implementation on clause elimination.
pub mod clause_manage;
/// Subsumption based Var/Clause Elimiantor
pub mod eliminator;
/// struct Solver
pub mod solver;
/// Implementation on Main algorithm.
pub mod solver_propagate;
/// Implementation on solver restart.
pub mod solver_restart;
/// Plumping layer.
pub mod types;
/// Var
pub mod var;
/// validates
pub mod validator;

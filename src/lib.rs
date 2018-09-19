//! This is a SAT solver in Rust.
#[macro_use]
mod macros;
/// Clause
pub mod clause;
/// struct Solver
pub mod solver;
/// Implementation on solver restart.
pub mod restart;
/// Plumping layer.
pub mod types;
/// Var
pub mod var;
/// Implementation on decision var selection.
pub mod var_manage;
/// validates
pub mod validator;

//! This is a SAT solver in Rust.
#[macro_use]
mod macros;
/// Clause
pub mod clause;
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
/// Implementation on decision var selection.
pub mod var_manage;

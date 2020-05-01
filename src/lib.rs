#![doc(html_root_url = "https://docs.rs/splr/0.4.0")]
/*!
# A modern CDCL SAT solver in Rust

Splr is a pure Rustic SAT solver, based on [Glucose 4.1](https://www.labri.fr/perso/lsimon/glucose/).
It adopts various research results on SAT solvers:

- CDCL, watch literals, and so on from [Minisat](http://minisat.se) and the ancestors
- Glucose-like dynamic blocking/forcing restarts based on [EMAs](https://arxiv.org/abs/1506.08905)
- heuristics adaptation
- pre/in-process simplification based on clause subsumption and variable elimination
- Learning Rate Based Branching and Reason Side Rewarding

*Many thanks to SAT researchers.*
*/
/// Crate `assign` implements Boolean Constraint Propagation and decision var selection.
pub mod assign;
/// Crate `cdb` provides `clause` object and its manager `ClauseDB`
pub mod cdb;
/// Crate `config` provides solver's configuration and CLI.
#[cfg_attr(not(feature = "no_IO"), path = "config.rs")]
#[cfg_attr(feature = "no_IO", path = "config_no_io.rs")]
pub mod config;
/// Crate `processor` implements a simplifier: clause subsumption and var elimination.
pub mod processor;
/// Crate `solver` provides the top-level API as a SAT solver.
pub mod solver;
/// Crate `state` is a collection of internal data.
pub mod state;
/// Crate `types` provides various building blocks, including some common traits.
pub mod types;

pub use {
    config::Config,
    solver::{Certificate, SatSolverIF, Solver, ValidateIF},
    types::SolverError,
};

/// Splr version number.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[macro_use]
extern crate bitflags;

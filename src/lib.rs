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
#[cfg(not(feature = "no_IO"))]
pub mod config;
#[cfg(feature = "no_IO")]
pub mod config_no_io;
/// Crate `processor` implements a simplifier: clause subsumption and var elimination.
pub mod processor;
/// Crate `solver` provides the top-level API as a SAT solver.
pub mod solver;
/// Crate `state` is a collection of internal data.
pub mod state;
/// Crate `types` provides various building blocks, including some common traits.
pub mod types;

/// Crate `config` provides solver's configuration and CLI.
#[cfg(not(feature = "no_IO"))]
pub use self::config::Config;
/// Crate `config` provides solver's configuration and CLI.
#[cfg(feature = "no_IO")]
pub use self::config_no_io::Config;

#[macro_use]
extern crate bitflags;

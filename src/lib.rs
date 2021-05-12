#![allow(clippy::upper_case_acronyms)]
/*!
# A modern CDCL SAT solver in Rust

Splr is a pure Rustic SAT solver, based on [Glucose 4.1](https://www.labri.fr/perso/lsimon/glucose/).
It adopts various research results on SAT solvers:

- CDCL, watch literals, and so on from [Minisat](http://minisat.se) and the ancestors
- Glucose-like dynamic blocking/forcing restarts based on [EMAs](https://arxiv.org/abs/1506.08905)
- heuristics adaptation
- pre/in-process simplification based on clause subsumption and variable elimination
- Chronological backtrack and non-chronological backjump
- Learning Rate Based Branching and Reason Side Rewarding
- Rephase
- Search stabilization
- clause vivification

*Many thanks to SAT researchers.*

# Examples

## Build a solver from a configuration based on a CNF file, then solve it.

```
use splr::*;

let config = Config::from("cnfs/sample.cnf");
if let Ok(mut s) = Solver::build(&config) {
    if let Ok(ans) = s.solve() {
        println!("{:?}", ans);
    }
}
```

## On-memory direct conversion from a vec to a solution

```
use {splr::*, std::convert::TryFrom};

let v: Vec<Vec<i32>> = vec![vec![1, 2], vec![-1, 3], vec![1, -3], vec![-1, 2]];
match Certificate::try_from(v).expect("panic!") {
    Certificate::UNSAT => 0,
    Certificate::SAT(vec) => vec.len(),
};
```

## Incremental solver

Splr provides 'incremental solver mode' if you built it with feature 'incremental_solver'.
This document covers extra functions only if you built it with `cargo doc --features incremental_solver`.

*/
/// Crate `assign` implements Boolean Constraint Propagation and decision var selection.
pub mod assign;
/// Crate `cdb` provides [`Clause`](`crate::cdb::Clause`) object and its manager [`ClauseDB`](`crate::cdb::ClauseDB`).
pub mod cdb;
/// Crate `config` provides solver's configuration and CLI.
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
    solver::{Certificate, SatSolverIF, SolveIF, Solver, ValidateIF},
    types::{Ema, Ema2, EmaIF, PropertyDereference, PropertyReference, SolverError},
};

/// Splr version number.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[macro_use]
extern crate bitflags;

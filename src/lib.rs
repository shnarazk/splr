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
use std::path::Path;

let config = Config::from(Path::new("cnfs/sample.cnf"));
if let Ok(mut s) = Solver::build(&config) {
    if let Ok(ans) = s.solve() {
        println!("{:?}", ans);
    }
}
```

## On-memory direct conversion from a vec to a solution

```
use splr::*;

let v: Vec<Vec<i32>> = vec![vec![1, 2], vec![-1, 3], vec![1, -3], vec![-1, 2]];
match Certificate::try_from(v).expect("panic!") {
    Certificate::UNSAT => 0,
    Certificate::SAT(vec) => vec.len(),
};
```

*/
/// Module `assign` implements Boolean Constraint Propagation and decision var selection.
pub mod assign;
/// Module `cdb` provides [`Clause`](`crate::cdb::Clause`) object and its manager [`ClauseDB`](`crate::cdb::ClauseDB`).
pub mod cdb;
/// Module `cnf` provides basic operations on CNF files
pub mod cnf;
/// Module `config` provides solver's configuration and CLI.
pub mod config;
/// Module `processor` implements a simplifier: clause subsumption and var elimination.
pub mod processor;
/// Module `solver` provides the top-level API as a SAT solver.
pub mod solver;
/// Module `state` is a collection of internal data.
pub mod state;
/// Module `types` provides various building blocks, including some common traits.
pub mod types;
/// Module `vam` provides variable activity manager.
pub mod vam;
/// Module `var_vector` provides a static mut vector of vars.
pub mod var_vector;

pub use {
    config::Config,
    solver::{Certificate, SatSolverIF, SolveIF, Solver, ValidateIF},
    types::*,
};

/// Splr version number.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[macro_use]
extern crate bitflags;

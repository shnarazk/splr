//! Crate 'solver' provides the top-level API as a SAT solver.
/// API to instantiate
mod build;
/// Crate 'conflict' handles conflicts.
mod conflict;
/// Crate `restart` provides restart heuristics.
mod restart;
/// CDCL search engine
mod search;
/// Crate `validate` implements a model checker.
mod validate;

pub use self::{
    build::SatSolverIF,
    restart::{RestartIF, RestartMode, Restarter},
    search::SolveIF,
    validate::ValidateIF,
};

use {
    crate::{assign::AssignStack, cdb::ClauseDB, processor::Eliminator, state::*, types::*},
    std::convert::TryFrom,
};

/// Normal results returned by Solver.
#[derive(Debug, PartialEq)]
pub enum Certificate {
    SAT(Vec<i32>),
    UNSAT,
}

/// The return type of `Solver::solve`.
/// This captures the following three cases:
/// * `Certificate::SAT` -- solved with a satisfiable assignment set,
/// * `Certificate::UNSAT` -- proved that it's an unsatisfiable problem, and
/// * `SolverException::*` -- caused by a bug
pub type SolverResult = Result<Certificate, SolverError>;

/// The SAT solver object consisting of 6 sub modules.
/// ```
/// use std::convert::TryFrom;
/// use crate::splr::{assign::{AssignIF, VarManipulateIF}, state::{State, StateIF}, types::*};
/// use crate::splr::solver::{SatSolverIF, Solver, Certificate::*};
///
/// let mut s = Solver::try_from("tests/sample.cnf").expect("can't load");
/// assert!(matches!(s.asg.var_stats(), (250,_, _, 250)));
/// if let Ok(SAT(v)) = s.solve() {
///     assert_eq!(v.len(), 250);
///     // But don't expect `s.asg.var_stats().3 == 0` at this point.
///     // It returns the number of vars which were assigned at decision level 0.
/// } else {
///     panic!("It should be satisfied!");
/// }
/// assert_eq!(Solver::try_from("tests/unsat.cnf").expect("can't load").solve(), Ok(UNSAT));
/// ```
#[derive(Debug)]
pub struct Solver {
    /// assignment management
    pub asg: AssignStack,
    /// clause container
    pub cdb: ClauseDB,
    /// clause and variable elimination
    pub elim: Eliminator,
    /// restart management
    pub rst: Restarter,
    /// misc data holder
    pub state: State,
}

impl TryFrom<Vec<Vec<i32>>> for Certificate {
    type Error = SolverError;
    fn try_from(vec: Vec<Vec<i32>>) -> Result<Certificate, Self::Error> {
        let s = Solver::try_from((Config::default(), vec.as_ref()));
        s.map_or_else(|e| e, |mut solver| solver.solve())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assign::VarManipulateIF;
    #[test]
    fn test_solver() {
        let config = Config::from("tests/sample.cnf");
        if let Ok(s) = Solver::build(&config) {
            assert!(matches!(s.asg.var_stats(), (250, _, _, 250)));
        } else {
            panic!("failed to build a solver for tests/sample.cnf");
        }
    }
}

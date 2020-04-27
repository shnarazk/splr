/// Crate 'solver' provides the top-level API as a SAT solver.
mod analyze;
mod build;
mod search;

use self::{build::SatSolverBuildIF, search::SatSolverSearchIF};

use crate::{
    assign::AssignStack, cdb::ClauseDB, eliminate::Eliminator, restart::Restarter, state::State,
    types::*,
};

/// API for SAT solver like `build`, `solve` and so on.
pub trait SatSolverIF: SatSolverBuildIF + SatSolverSearchIF {
    /// add a vector of `Lit` as a clause to the solver.
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
    /// make a solver and load a CNF into it.
    ///
    /// # Errors
    ///
    /// IO error by failing to load a CNF file.
    fn build(config: &Config) -> Result<Solver, SolverError>;
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solve(&mut self) -> SolverResult;
}

impl SatSolverIF for Solver {
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId> {
        self.solver_add_unchecked_clause(v)
    }
    fn build(config: &Config) -> Result<Solver, SolverError> {
        <Solver as SatSolverBuildIF>::solver_build(config)
    }
    fn solve(&mut self) -> SolverResult {
        <Solver as SatSolverSearchIF>::solve(self)
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
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

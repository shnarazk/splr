//! Crate `validator` implements a model checker.
use crate::{
    assign::{AssignIF, PropagateIF},
    cdb::ClauseDBIF,
    solver::Solver,
    types::{Lit, MaybeInconsistent, SolverError},
};

/// API for SAT validator like [`inject_assignment`](`crate::solver::ValidateIF::inject_assignment`), [`validate`](`crate::solver::ValidateIF::validate`) and so on.
pub trait ValidateIF {
    /// load a assignment set into solver.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn inject_assignment(&mut self, vec: &[i32]) -> MaybeInconsistent;
    /// return `true` is the loaded assignment set is satisfiable (a model of a problem).
    fn validate(&self) -> Option<Vec<i32>>;
}

impl ValidateIF for Solver {
    /// inject an assignment set into solver.
    /// An assignment set is represented by a list of `i32`.
    ///
    /// #Example
    ///
    /// ```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use splr::solver::{Solver, ValidateIF};
    ///
    /// let cnf = CNFDescription {
    ///         num_of_variables: 4,
    ///         ..CNFDescription::default()
    ///     };
    /// let mut s = Solver::instantiate(&Config::default(), &cnf);
    /// assert_eq!(s.inject_assignment(&[1i32, -2, 3]), Ok(()));
    ///```
    ///
    fn inject_assignment(&mut self, vec: &[i32]) -> MaybeInconsistent {
        if vec.is_empty() {
            return Err(SolverError::Inconsistent);
        }
        for i in vec {
            self.asg.assign_at_root_level(Lit::from(*i))?;
        }
        Ok(())
    }
    /// returns None if the given assignment is a model of a problem.
    /// Otherwise returns a clause which is not satisfiable under a given assignment.
    ///
    /// #Example
    ///
    /// ```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use splr::solver::{Solver, ValidateIF};
    ///
    /// let cnf = CNFDescription {
    ///         num_of_variables: 4,
    ///         ..CNFDescription::default()
    ///     };
    /// let mut s = Solver::instantiate(&Config::default(), &cnf);
    /// s.inject_assignment(&[1i32, -2, 3]);
    /// assert_eq!(s.validate(), None);
    ///```
    ///
    fn validate(&self) -> Option<Vec<i32>> {
        self.cdb
            .validate(&self.asg.assign_ref(), true)
            .map(|cid| Vec::<i32>::from(&self.cdb[cid]))
    }
}

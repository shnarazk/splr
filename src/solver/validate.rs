//! Crate `validator` implements a model checker.
use crate::{
    assign::{AssignIF, AssignStack},
    cdb::ClauseDBIF,
    solver::{propagate::*, Solver},
    types::{Lit, MaybeInconsistent, SolverError, Var},
};

/// API for SAT validator like [`inject_assignment`](`crate::solver::ValidateIF::inject_assignment`), [`validate`](`crate::solver::ValidateIF::validate`) and so on.
pub trait ValidateIF<'a> {
    /// load a assignment set into solver.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn inject_assignment(&'a mut self, vec: &[i32]) -> MaybeInconsistent;
    /// return `true` is the loaded assignment set is satisfiable (a model of a problem).
    fn validate(&self) -> Option<Vec<i32>>;
}

impl<'a> ValidateIF<'a> for Solver<'a> {
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
    fn inject_assignment(&'a mut self, vec: &[i32]) -> MaybeInconsistent {
        if vec.is_empty() {
            return Err(SolverError::Inconsistent);
        }
        for i in vec {
            {
                // let vars: &'a mut Vec<Var<'a>> = &mut self.vars;
                // let asg: &'a mut AssignStack<'a> = &mut self.asg;
                // let vam: &'a mut _ = &mut self.vam;
                let Solver { vars, asg, vam, .. } = self;
                cancel_until(vars, asg, vam, asg.root_level());
                // vars[i.unsigned_abs() as usize].assign = Some(*i < 0);
            }
            /*{
                let vars: &'a mut Vec<Var<'a>> = &mut self.vars;
                let asg: &'a mut AssignStack<'a> = &mut self.asg;
                let vam: &'a mut _ = &mut self.vam;
                let v: &'a Var = &vars[i.unsigned_abs() as usize];
                let l: Lit<'a> = Lit::from((v, *i < 0));
                // assign_at_root_level(asg, vam, l)?;
                asg.trail.push(l);
                // asg.make_var_asserted(heap, v);
                todo!();
            }*/
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
            .validate(
                &self
                    .vars
                    .iter()
                    .map(|v: &Var<'_>| v.assign)
                    .collect::<Vec<_>>(),
                true,
            )
            .map(|cid| Vec::<i32>::from(&self.cdb[cid]))
    }
}

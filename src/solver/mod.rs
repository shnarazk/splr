/// Crate `solver` provides the top-level API as a SAT solver.
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
/// Implement vivification preprocessor
mod vivify;

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
    /// It is satisfiable; `vec` is such an assignment sorted by var order.
    SAT(Vec<i32>),
    /// It is unsatisfiable.
    UNSAT,
}

/// The return type of `Solver::solve`.
/// This captures the following three cases:
/// * `Certificate::SAT` -- solved with a satisfiable assignment set,
/// * `Certificate::UNSAT` -- proved that it's an unsatisfiable problem, and
/// * `SolverException::*` -- caused by a bug
pub type SolverResult = Result<Certificate, SolverError>;

/// define sub-modules' responsibilities
#[derive(Clone, Copy, Debug)]
pub enum SolverEvent {
    /// set up internal parameters.
    /// # CAVEAT
    /// some implementation might have a special premise to call: decision_level == 0.
    Adapt((SearchStrategy, usize), usize),
    /// asserting a var.
    Assert(VarId),
    /// conflict by unit propagation.
    Conflict,
    /// eliminating a var.
    Eliminate(VarId),
    /// Not in use
    Instantiate,
    /// increment the number of vars.
    NewVar,
    /// re-initialization for incremental solving.
    Reinitialize,
    /// stabilization update.
    Stabilize((bool, bool)),
    /// Vivification: `true` for start, `false` for end.
    Vivify(bool),
}

/// The SAT solver object consisting of 6 sub modules.
/// ```
/// use std::convert::TryFrom;
/// use crate::splr::*;
/// use crate::splr::{assign::{AssignIF, VarManipulateIF}, state::{State, StateIF}, types::*};
///
/// let mut s = Solver::try_from("tests/sample.cnf").expect("can't load");
/// assert!(matches!(s.asg.var_stats(), (250,_, _, 250, _)));
/// if let Ok(Certificate::SAT(v)) = s.solve() {
///     assert_eq!(v.len(), 250);
///     // But don't expect `s.asg.var_stats().3 == 0` at this point.
///     // It returns the number of vars which were assigned at decision level 0.
/// } else {
///     panic!("It should be satisfied!");
/// }
/// assert_eq!(Solver::try_from("tests/unsat.cnf").expect("can't load").solve(), Ok(Certificate::UNSAT));
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

impl<V> TryFrom<Vec<V>> for Certificate
where
    V: AsRef<[i32]>,
{
    type Error = SolverError;
    fn try_from(vec: Vec<V>) -> SolverResult {
        let s = Solver::try_from((Config::default(), vec.as_ref()));
        s.map_or_else(|e| e, |mut solver| solver.solve())
    }
}

/// Iterator for Solver
/// * takes `&mut Solver`
/// * returns `Option<Vec<i32>>`
///    * `Some(Vec<i32>)` -- satisfiable assignment
///    * `None` -- unsatisfiable anymore
/// * Some internal error causes panic.
#[cfg(feature = "incremental_solver")]
pub struct SolverIter<'a> {
    solver: &'a mut Solver,
    refute: Option<Vec<i32>>,
}

#[cfg(feature = "incremental_solver")]
impl Solver {
    /// return an iterator on Solver. **Requires 'incremental_solver' feature**
    ///```
    ///for v in Solver::try_from("tests/sample.cnf").expect("panic").iter() {
    ///    println!(" - answer: {:?}", v);
    ///}
    ///```
    pub fn iter(&mut self) -> SolverIter {
        SolverIter {
            solver: self,
            refute: None,
        }
    }
}

#[cfg(feature = "incremental_solver")]
impl<'a> Iterator for SolverIter<'a> {
    type Item = Vec<i32>;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref v) = self.refute {
            match self.solver.add_clause(v) {
                Err(SolverError::Inconsistent) => return None,
                Err(e) => panic!("s UNKNOWN: {:?}", e),
                Ok(_) => self.solver.reset(),
            }
            self.refute = None;
        }
        match self.solver.solve() {
            Ok(Certificate::SAT(ans)) => {
                let rft: Vec<i32> = ans.iter().map(|i| -i).collect::<Vec<i32>>();
                self.refute = Some(rft);
                Some(ans)
            }
            Ok(Certificate::UNSAT) => None,
            e => panic!("s UNKNOWN: {:?}", e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assign::VarManipulateIF;
    use std::convert::{From, TryFrom};

    #[cfg_attr(not(feature = "no_IO"), test)]
    fn test_solver() {
        let config = Config::from("tests/sample.cnf");
        if let Ok(s) = Solver::build(&config) {
            assert!(matches!(s.asg.var_stats(), (250, _, _, 250)));
        } else {
            panic!("failed to build a solver for tests/sample.cnf");
        }
    }

    macro_rules! run {
        ($vec: expr) => {
            println!(
                "{:>46} =| {:?}",
                format!("{:?}", $vec),
                match Solver::try_from((Config::default(), $vec.as_ref())).map(|mut s| s.solve()) {
                    Err(e) => e,
                    Ok(Ok(u @ Certificate::UNSAT)) => Ok(u),
                    Ok(s) => s,
                }
            );
        };
    }

    macro_rules! sat {
        ($vec: expr) => {
            println!(
                "{:>46} =| {:?}",
                format!("{:?}", $vec),
                Certificate::try_from($vec)
            );
        };
    }

    #[test]
    fn test_on_memory_solving() {
        let mut v: Vec<Vec<i32>> = Vec::new();
        run!(v);
        v.push(Vec::new());
        run!(v);
        run!(vec![vec![1]]);
        run!(vec![vec![1], vec![-1]]);
        run!(vec![vec![1, 2], vec![-1, 3], vec![1, -3], vec![-1, 2]]);
        run!(vec![
            vec![1, 2],
            vec![-1, 3],
            vec![1, -3],
            vec![-1, -2],
            vec![-2, -3]
        ]);
        run!(vec![
            vec![1, 2],
            vec![-1, 3],
            vec![-1, -3],
            vec![-1, -2],
            vec![1, -2]
        ]);

        // auto conversion via `as_ref`
        let (v1, v2, v3, v4, v5) = (vec![1, 2], vec![-1, 3], vec![1, -3], vec![-1, 2], vec![-3]);
        run!(vec![&v1, &v2, &v3, &v4, &v5]); // : Vec<&[i32]>
        run!([&v1, &v2, &v3, &v4, &v5]); // [&[i32]; 5]

        // let v: Vec<Vec<i32>> = vec![vec![1, 2], vec![-1, 3], vec![1, -3], vec![-1, 2]];
        // let s = Solver::try_from((Config::default(), v.as_ref()));
        // match s.map_or_else(|e| e, |mut solver| solver.solve()) {
        //     Ok(Certificate::SAT(ans)) => println!("s SATISFIABLE: {:?}", ans),
        //     Ok(Certificate::UNSAT) => println!("s UNSATISFIABLE"),
        //     Err(e) => panic!("{}", e),
        // }
        let v0: Vec<Vec<i32>> = Vec::new();
        sat!(v0);
        let v1: Vec<Vec<i32>> = Vec::from(Vec::new());
        sat!(v1);
        sat!(vec![vec![1i32]]);
        sat!(vec![vec![1i32], vec![-1]]);
        sat!(vec![vec![1i32, 2], vec![-1, 3], vec![1, -3], vec![-1, 2]]);
        sat!(vec![
            vec![1i32, 2],
            vec![-1, 3],
            vec![1, -3],
            vec![-1, -2],
            vec![-2, -3]
        ]);
        sat!(vec![
            vec![1i32, 2],
            vec![-1, 3],
            vec![-1, -3],
            vec![-1, -2],
            vec![1, -2]
        ]);
        let (v1, v2, v3, v4, v5) = (
            vec![1i32, 2],
            vec![-1i32, 3],
            vec![1i32, -3],
            vec![-1i32, 2],
            vec![-3i32],
        );
        sat!(vec![&v1, &v2, &v3, &v4, &v5]); // : Vec<&[i32]>
    }
}

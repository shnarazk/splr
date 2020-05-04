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
/// use crate::splr::*;
/// use crate::splr::{assign::{AssignIF, VarManipulateIF}, state::{State, StateIF}, types::*};
///
/// let mut s = Solver::try_from("tests/sample.cnf").expect("can't load");
/// assert!(matches!(s.asg.var_stats(), (250,_, _, 250)));
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
    fn try_from(vec: Vec<V>) -> Result<Certificate, Self::Error> {
        let s = Solver::try_from((Config::default(), vec.as_ref()));
        s.map_or_else(|e| e, |mut solver| solver.solve())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assign::VarManipulateIF;
    use std::convert::TryFrom;

    #[test]
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
        let mut v: Vec<Vec<i32>> = Vec::new();
        sat!(v);
        v.push(Vec::new());
        sat!(v);
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

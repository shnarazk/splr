/// Module `solver` provides the top-level API as a SAT solver.
/// API to instantiate
mod build;
/// Module 'conflict' handles conflicts.
mod conflict;
/// Module `restart` provides restart heuristics.
pub mod restart;
/// CDCL search engine
mod search;
/// Stage manger (was Stabilizer)
mod stage;
/// Module `validate` implements a model checker.
mod validate;

pub use self::{
    build::SatSolverIF,
    restart::{RestartIF, RestartManager},
    search::SolveIF,
    stage::StageManager,
    validate::ValidateIF,
};

use crate::{assign::AssignStack, cdb::ClauseDB, state::*, types::*};

/// Normal results returned by Solver.
#[derive(Debug, Eq, PartialEq)]
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
/// * `SolverError::*` -- caused by a bug
pub type SolverResult = Result<Certificate, SolverError>;

/// define sub-modules' responsibilities
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SolverEvent {
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
    /// restart
    Restart,
    /// start a new stage of Luby stabilization. It holds new scale.
    Stage(usize),

    #[cfg(feature = "clause_vivification")]
    /// Vivification: `true` for start, `false` for end.
    Vivify(bool),
}

/// The SAT solver object consisting of 6 sub modules.
/// ```
/// use crate::splr::*;
/// use crate::splr::{state::{State, StateIF}, types::*, var_vector::VarRef};
/// use std::path::Path;
///
/// let mut s = Solver::try_from(Path::new("cnfs/sample.cnf")).expect("can't load");
/// assert_eq!(VarRef::num_vars(), 250);
/// assert_eq!(s.asg.num_unasserted_vars(), 250);
/// if let Ok(Certificate::SAT(v)) = s.solve() {
///     assert_eq!(v.len(), 250);
///     // But don't expect `s.asg.var_stats().3 == 0` at this point.
///     // It returns the number of vars which were assigned at decision level 0.
/// } else {
///     panic!("It should be satisfied!");
/// }
/// assert_eq!(Solver::try_from(Path::new("cnfs/unsat.cnf")).expect("can't load").solve(), Ok(Certificate::UNSAT));
/// ```
#[derive(Clone, Debug, Default)]
pub struct Solver {
    /// assignment management
    pub asg: AssignStack,
    /// clause container
    pub cdb: ClauseDB,
    /// misc data holder
    pub state: State,
}

/// Example
///```
/// use crate::splr::*;
///
/// let v: Vec<Vec<i32>> = vec![];
/// assert!(matches!(
///     Certificate::try_from(v),
///     Ok(Certificate::SAT(_))
/// ));
/// assert!(matches!(
///     Certificate::try_from(vec![vec![0_i32]]),
///     Err(SolverError::InvalidLiteral)
/// ));
///
/// // `Solver` has another interface.
/// assert!(matches!(
///     Solver::try_from((Config::default(), vec![vec![0_i32]].as_ref())),
///     Err(Err(SolverError::InvalidLiteral))
/// ));
///```
impl<V: AsRef<[i32]>> TryFrom<Vec<V>> for Certificate {
    type Error = SolverError;
    fn try_from(vec: Vec<V>) -> SolverResult {
        Solver::try_from((Config::default(), vec.as_ref())).map_or_else(
            |e: SolverResult| match e {
                Ok(cert) => Ok(cert),
                Err(SolverError::EmptyClause) => Ok(Certificate::UNSAT),
                Err(e) => Err(e),
            },
            |mut solver| solver.solve(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::var_vector::VarRef;

    #[cfg_attr(not(feature = "no_IO"), test)]
    fn test_solver() {
        let config = Config::from("cnfs/sample.cnf");
        if let Ok(s) = Solver::build(&config) {
            assert_eq!(VarRef::num_vars(), 250);
            assert_eq!(s.asg.num_unasserted_vars(), 250);
        } else {
            panic!("failed to build a solver for cnfs/sample.cnf");
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
        ($vec: expr, $should_be: pat) => {
            println!("{:>46} =| ", format!("{:?}", $vec));
            let result = Certificate::try_from($vec);
            println!("{:?}", result);
            assert!(matches!(result, $should_be));
        };
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
        let v0: Vec<Vec<i32>> = vec![];
        sat!(v0, Ok(Certificate::SAT(_)));
        let v1: Vec<Vec<i32>> = vec![vec![]];
        sat!(v1, Ok(Certificate::UNSAT));
        sat!(vec![vec![1i32]], Ok(Certificate::SAT(_)));
        sat!(vec![vec![1i32], vec![-1]], Ok(Certificate::UNSAT));
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

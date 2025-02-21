//! Module `types' provides various building blocks, including
//! some common traits.

/// methods on clause
pub mod clause;
/// methods on CNF file
pub mod cnf;
/// methods on clause activity
pub mod ema;
/// methods on flags used in Var and Clause
pub mod flags;
/// types used as index
pub mod idx;
/// methods on literals
pub mod lit;
/// methods on binary link, namely binary clause
pub mod luby;
/// methods on f64 sort
pub mod ordered_proxy;
/// methods on Var
pub mod var;

pub use self::{
    clause::*, cnf::*, ema::*, flags::*, idx::*, lit::*, luby::*, ordered_proxy::*, var::*,
};

pub use crate::{assign::AssignReason, config::Config, solver::SolverEvent};

use std::{fmt, fs::File};

/// API for accessing internal data in a module.
/// For example, `State::progress` needs to access misc parameters and statistics,
/// which, however, should be used locally in the defining modules.
/// To avoid to make them public, we define a generic accessor or exporter here.
pub trait PropertyReference<I, O> {
    fn refer(&self, key: I) -> &O;
}

pub trait PropertyDereference<I, O: Sized> {
    fn derefer(&self, key: I) -> O;
}

/// API for reward based activity management.
pub trait ActivityIF<Ix> {
    /// return one's activity.
    fn activity(&self, ix: Ix) -> f64;
    /// set activity
    fn set_activity(&mut self, ix: Ix, val: f64);
    /// modify one's activity at conflict analysis in `conflict_analyze` in [`solver`](`crate::solver`).
    fn reward_at_analysis(&mut self, _ix: Ix) {
        #[cfg(feature = "boundary_check")]
        todo!()
    }
    /// modify one's activity at value assignment in assign.
    fn reward_at_assign(&mut self, _ix: Ix) {
        #[cfg(feature = "boundary_check")]
        todo!()
    }
    /// modify one's activity at value assignment in unit propagation.
    fn reward_at_propagation(&mut self, _ix: Ix) {
        #[cfg(feature = "boundary_check")]
        todo!()
    }
    /// modify one's activity at value un-assignment in [`cancel_until`](`crate::assign::PropagateIF::cancel_until`).
    fn reward_at_unassign(&mut self, _ix: Ix) {
        #[cfg(feature = "boundary_check")]
        todo!()
    }
    /// update reward decay.
    fn update_activity_decay(&mut self, _decay: f64);
    /// update internal counter.
    fn update_activity_tick(&mut self);
}

/// API for object instantiation based on `Configuration` and `CNFDescription`.
/// This is implemented by *all the Splr modules* except `Configuration` and `CNFDescription`.
///
/// # Example
///
/// ```
/// use crate::{splr::config::Config, splr::types::*};
/// use splr::{cdb::ClauseDB, solver::Solver};
/// let _ = ClauseDB::instantiate(&Config::default(), &CNFDescription::default());
/// let _ = Solver::instantiate(&Config::default(), &CNFDescription::default());
///```
pub trait Instantiate {
    /// make and return an object from `Config` and `CNFDescription`.
    fn instantiate(conf: &Config, cnf: &CNFDescription) -> Self;
    /// update by a solver event.
    fn handle(&mut self, _e: SolverEvent) {}
}

/// API for O(n) deletion from a list, providing `delete_unstable`.
pub trait Delete<T> {
    /// *O(n)* item deletion protocol.
    fn delete_unstable<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
}

/// Capture a conflict
pub type ConflictContext = (Lit, AssignReason);

/// Return type of unit propagation
pub type PropagationResult = Result<(), ConflictContext>;

/// Internal errors.
/// Note: returning `Result<(), a-singleton>` is identical to returning `bool`.
#[derive(Debug, Eq, PartialEq)]
pub enum SolverError {
    // StateUNSAT = 0,
    // StateSAT,
    // A given CNF contains empty clauses or derives them during reading
    EmptyClause,
    // A clause contains a literal out of the range defined in its header.
    // '0' is an example.
    InvalidLiteral,
    // Exceptions caused by file operations
    IOError,
    // UNSAT with some internal context
    Inconsistent,
    OutOfMemory,
    // UNSAT with some internal context
    RootLevelConflict(ConflictContext),
    TimeOut,
    SolverBug,
    // For now, this is used for catching errors relating to clock
    UndescribedError,
}

impl fmt::Display for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// A Return type used by solver functions.
pub type MaybeInconsistent = Result<(), SolverError>;

impl<T> Delete<T> for Vec<T> {
    fn delete_unstable<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool,
    {
        if let Some(i) = self.iter().position(filter) {
            self.swap_remove(i);
        }
    }
}

#[derive(Debug, Default)]
pub struct Logger {
    dest: Option<File>,
}

impl fmt::Display for Logger {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Dump({:?})", self.dest)
    }
}

impl Logger {
    pub fn new<T: AsRef<str>>(fname: T) -> Self {
        Logger {
            dest: File::create(fname.as_ref()).ok(),
        }
    }
    pub fn dump(&mut self, mes: String) {
        use std::io::Write;
        if let Some(f) = &mut self.dest {
            f.write_all(&mes.into_bytes())
                .unwrap_or_else(|_| panic!("fail to dump {f:?}"));
        } else {
            println!("{mes}");
        }
    }
}

#[cfg(feature = "boundary_check")]
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Propagate {
    None,
    CacheSatisfied(usize),
    FindNewWatch(usize, Lit, Lit),
    BecameUnit(usize, Lit),
    EmitConflict(usize, Lit),
    SandboxCacheSatisfied(usize),
    SandboxFindNewWatch(usize, Lit, Lit),
    SandboxBecameUnit(usize),
    SandboxEmitConflict(usize, Lit),
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn test_cnf() {
        if let Ok(reader) = CNFReader::try_from(Path::new("cnfs/sample.cnf")) {
            assert_eq!(reader.cnf.num_of_variables, 250);
            assert_eq!(reader.cnf.num_of_clauses, 1065);
        } else {
            panic!("failed to load cnfs/sample.cnf");
        }
    }
}

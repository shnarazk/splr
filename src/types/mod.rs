/// methods on clause activity
pub mod ema;
/// methods on literals
pub mod lit;
pub mod literal;
/// methods on Luby sequence
pub mod luby;
/// methods on variables
pub mod var;

pub use self::{ema::*, lit::*, luby::*, var::*};

/// Module `types' provides various building blocks, including
/// some common traits.
pub use crate::{
    assign::AssignReason,
    cdb::{Clause, ClauseDB, ClauseIF, ClauseId, ClauseIdIF},
    config::Config,
    solver::SolverEvent,
    // types::*,
};

use std::{
    cmp::Ordering,
    fmt,
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

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

/// Decision Level Representation.
pub type DecisionLevel = u32;

// impl<'a> Index<Lit<'a>> for [bool] {
//     type Output = bool;
//     #[inline]
//     fn index(&self, l: Lit) -> &Self::Output {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.get_unchecked(usize::from(l))
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self[usize::from(l)]
//     }
// }

// impl<'a> IndexMut<Lit<'a>> for [bool] {
//     #[inline]
//     fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.get_unchecked_mut(usize::from(l))
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self[usize::from(l)]
//     }
// }

// impl<'a> Index<Lit<'a>> for Vec<bool> {
//     type Output = bool;
//     #[inline]
//     fn index(&'a self, l: Lit<'a>) -> &'a Self::Output {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.get_unchecked(usize::from(l))
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self[usize::from(l)]
//     }
// }

// impl<'a> IndexMut<Lit<'a>> for Vec<bool> {
//     #[inline]
//     fn index_mut(&'a mut self, l: Lit<'a>) -> &'a mut Self::Output {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.get_unchecked_mut(usize::from(l))
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self[usize::from(l)]
//     }
// }

/// Capture a conflict
pub type ConflictContext<'a> = (Lit<'a>, AssignReason<'a>);

/// Return type of unit propagation
pub type PropagationResult<'a> = Result<(), ConflictContext<'a>>;

// A generic reference to a clause or something else.
// we can use DEAD for simply satisfied form, f.e. an empty forms,
// while EmptyClause can be used for simply UNSAT form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RefClause<'a> {
    Clause(ClauseId),
    Dead,
    EmptyClause,
    RegisteredClause(ClauseId),
    UnitClause(Lit<'a>),
}

impl RefClause<'_> {
    pub fn as_cid(&self) -> ClauseId {
        match self {
            RefClause::Clause(cid) => *cid,
            RefClause::RegisteredClause(cid) => *cid,
            _ => panic!("invalid reference to clause"),
        }
    }
    pub fn is_new(&self) -> Option<ClauseId> {
        match self {
            RefClause::Clause(cid) => Some(*cid),
            RefClause::RegisteredClause(_) => None,
            RefClause::EmptyClause => None,
            RefClause::Dead => None,
            RefClause::UnitClause(_) => None,
        }
    }
}

/// Internal errors.
/// Note: returning `Result<(), a-singleton>` is identical to returning `bool`.
#[derive(Clone, Debug, Eq, PartialEq)]
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
    RootLevelConflict,
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

/// CNF locator
#[derive(Clone, Debug, Default)]
pub enum CNFIndicator {
    /// not specified
    #[default]
    Void,
    /// from a file
    File(String),
    /// embedded directly
    LitVec(usize),
}

impl fmt::Display for CNFIndicator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CNFIndicator::Void => write!(f, "No CNF specified)"),
            CNFIndicator::File(file) => write!(f, "CNF file({file})"),
            CNFIndicator::LitVec(n) => write!(f, "A vec({n} clauses)"),
        }
    }
}

// impl CNFIndicator {
//     pub fn to_string(&self) -> String {
//         match self {
//             CNFIndicator::Void => "(no cnf)".to_string(),
//             CNFIndicator::File(f) => f.to_string(),
//             CNFIndicator::LitVec(v) => format!("(embedded {} element vector)", v.len()).to_string(),
//         }
//     }
// }

/// Data storage about a problem.
#[derive(Clone, Debug)]
pub struct CNFDescription {
    pub num_of_variables: usize,
    pub num_of_clauses: usize,
    pub pathname: CNFIndicator,
}

impl Default for CNFDescription {
    fn default() -> CNFDescription {
        CNFDescription {
            num_of_variables: 0,
            num_of_clauses: 0,
            pathname: CNFIndicator::Void,
        }
    }
}

impl fmt::Display for CNFDescription {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let CNFDescription {
            num_of_variables: nv,
            num_of_clauses: nc,
            pathname: path,
        } = &self;
        write!(f, "CNF({nv}, {nc}, {path})")
    }
}

impl<V: AsRef<[i32]>> From<&[V]> for CNFDescription {
    fn from(vec: &[V]) -> Self {
        let num_of_variables = vec
            .iter()
            .map(|clause| clause.as_ref().iter().map(|l| l.abs()).max().unwrap_or(0))
            .max()
            .unwrap_or(0) as usize;
        CNFDescription {
            num_of_variables,
            num_of_clauses: vec.len(),
            pathname: CNFIndicator::LitVec(vec.len()),
        }
    }
}

/// A wrapper structure to make a CNFDescription from a file.
/// To make CNFDescription clone-able, a BufReader should be separated from it.
/// If you want to make a CNFDescription which isn't connected to a file,
/// just call CNFDescription::default() directly.
#[derive(Debug)]
pub struct CNFReader {
    pub cnf: CNFDescription,
    pub reader: BufReader<File>,
}

impl TryFrom<&Path> for CNFReader {
    type Error = SolverError;
    fn try_from(path: &Path) -> Result<Self, Self::Error> {
        let pathname = if path.to_string_lossy().is_empty() {
            "--".to_string()
        } else {
            Path::new(&path.to_string_lossy().into_owned())
                .file_name()
                .map_or("aStrangeNamed".to_string(), |f| {
                    f.to_string_lossy().into_owned()
                })
        };
        let fs = File::open(path).map_or(Err(SolverError::IOError), Ok)?;
        let mut reader = BufReader::new(fs);
        let mut buf = String::new();
        let mut nv: usize = 0;
        let mut nc: usize = 0;
        let mut found_valid_header = false;
        loop {
            buf.clear();
            match reader.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_k) => {
                    let mut iter = buf.split_whitespace();
                    if iter.next() == Some("p") && iter.next() == Some("cnf") {
                        if let Some(v) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                            if let Some(c) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                                nv = v;
                                nc = c;
                                found_valid_header = true;
                                break;
                            }
                        }
                    }
                    continue;
                }
                Err(e) => {
                    println!("{e}");
                    return Err(SolverError::IOError);
                }
            }
        }
        if !found_valid_header {
            return Err(SolverError::IOError);
        }
        let cnf = CNFDescription {
            num_of_variables: nv,
            num_of_clauses: nc,
            pathname: CNFIndicator::File(pathname),
        };
        Ok(CNFReader { cnf, reader })
    }
}

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

/// API for object properties.
pub trait FlagIF {
    type FlagType;
    /// return true if the flag in on.
    fn is(&self, flag: Self::FlagType) -> bool;
    /// set the flag.
    fn set(&mut self, f: Self::FlagType, b: bool);
    // toggle the flag.
    fn toggle(&mut self, flag: Self::FlagType);
    /// toggle the flag off.
    fn turn_off(&mut self, flag: Self::FlagType);
    /// toggle the flag on.
    fn turn_on(&mut self, flag: Self::FlagType);
}

bitflags! {
    /// Misc flags used by [`Clause`](`crate::cdb::Clause`).
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct FlagClause: u8 {
        /// a clause is a generated clause by conflict analysis and is removable.
        const LEARNT       = 0b0000_0001;
        /// used in conflict analyze
        const USED         = 0b0000_0010;
        /// a clause or var is enqueued for eliminator.
        const ENQUEUED     = 0b0000_0100;
        /// a clause is registered in vars' occurrence list.
        const OCCUR_LINKED = 0b0000_1000;
        /// a given clause derived a learnt which LBD is smaller than 20.
        const DERIVE20     = 0b0001_0000;
    }
}

bitflags! {
    /// Misc flags used by [`Var`](`crate::assign::Var`).
    #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub struct FlagVar: u8 {
        /// * the previous assigned value of a Var.
        const PHASE        = 0b0000_0001;
        /// used in conflict analyze
        const USED         = 0b0000_0010;
        /// a var is eliminated and managed by eliminator.
        const ELIMINATED   = 0b0000_0100;
        /// a clause or var is enqueued for eliminator.
        const ENQUEUED     = 0b0000_1000;
        /// a var is checked during in the current conflict analysis.
        const CA_SEEN      = 0b0001_0000;

        #[cfg(feature = "debug_propagation")]
        /// check propagation
        const PROPAGATED   = 0b0010_0000;
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

#[derive(Clone, Debug)]
pub struct OrderedProxy<T: Clone + Sized> {
    index: f64,
    body: T,
}

// impl<T: Clone + Sized> Default for OrderedProxy<T> {
//     fn default() -> Self {
//         OrderedProxy {
//             index: 0.0,
//             body: T::default(),
//         }
//     }
// }

impl<T: Clone + Sized> PartialEq for OrderedProxy<T> {
    fn eq(&self, other: &OrderedProxy<T>) -> bool {
        self.index == other.index
    }
}

impl<T: Clone + Sized> Eq for OrderedProxy<T> {}

impl<T: Clone + PartialEq> PartialOrd for OrderedProxy<T> {
    fn partial_cmp(&self, other: &OrderedProxy<T>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Clone + PartialEq> Ord for OrderedProxy<T> {
    fn cmp(&self, other: &OrderedProxy<T>) -> Ordering {
        if let Some(ord) = self.index.partial_cmp(&other.index) {
            ord
        } else {
            match (self.index.is_nan(), self.index.is_nan()) {
                (true, true) => Ordering::Equal,
                (true, false) => Ordering::Greater,
                (false, true) => Ordering::Less,
                (false, false) => unreachable!(),
            }
        }
    }
}

impl<T: Clone + Sized> OrderedProxy<T> {
    pub fn new(body: T, index: f64) -> Self {
        OrderedProxy { index, body }
    }
    /// TODO: just use std::cmp::Reverse?
    pub fn new_invert(body: T, rindex: f64) -> Self {
        OrderedProxy {
            index: -rindex,
            body,
        }
    }
    pub fn to(&self) -> T {
        self.body.clone()
    }
    pub fn value(&self) -> f64 {
        self.index
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

#[cfg(feature = "boundary_check")]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum VarState {
    AssertedSandbox(usize),
    Assigned(usize),
    AssignedSandbox(usize),
    Propagated(usize),
    Unassigned(usize),
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

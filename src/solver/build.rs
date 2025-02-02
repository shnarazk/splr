//! Solver Builder

use {
    super::{
        propagate::*, Certificate, Solver, SolverEvent, SolverResult, State, StateIF,
        VarActivityManager,
    },
    crate::{
        assign::{AssignIF, AssignStack},
        cdb::{ClauseDB, ClauseDBIF},
        types::*,
    },
};

#[cfg(not(feature = "no_IO"))]
use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

/// API for SAT solver creation and modification.
pub trait SatSolverIF<'a>: Instantiate {
    /// add an assignment to Solver.
    ///
    /// # Errors
    ///
    /// * `SolverError::Inconsistent` if it conflicts with existing assignments.
    /// * `SolverError::InvalidLiteral` if it is out of range for var index.
    ///
    /// # Example
    ///
    /// ```
    /// use crate::splr::*;
    /// use crate::splr::assign::VarManipulateIF;    // for s.asg.assign()
    /// use std::path::Path;
    ///
    /// let mut s = Solver::try_from(Path::new("cnfs/uf8.cnf")).expect("can't load");
    /// assert!(s.add_assignment(1).is_ok());
    /// assert_eq!(s.asg.assign(1), Some(true));
    /// assert!(s.add_assignment(2).is_ok());
    /// assert!(s.add_assignment(3).is_ok());
    /// assert!(s.add_assignment(4).is_ok());
    /// assert!(s.add_assignment(5).is_ok());
    /// assert!(s.add_assignment(8).is_ok());
    /// assert!(matches!(s.add_assignment(-1), Err(SolverError::RootLevelConflict(_))));
    /// assert!(matches!(s.add_assignment(10), Err(SolverError::InvalidLiteral)));
    /// assert!(matches!(s.add_assignment(0), Err(SolverError::InvalidLiteral)));
    /// assert_eq!(s.solve(), Ok(Certificate::SAT(vec![1, 2, 3, 4, 5, -6, 7, 8])));
    /// ```
    fn add_assignment(&'a mut self, val: i32) -> Result<&'a mut Solver<'a>, SolverError>;
    /// add a literal to Solver.
    ///
    /// # Errors
    ///
    /// * `SolverError::Inconsistent` if a given clause is unit and conflicts with existing assignments.
    /// * `SolverError::InvalidLiteral` if a literal in it is out of range for var index.
    ///
    /// # Example
    ///```
    /// use crate::splr::*;
    /// use std::path::Path;
    ///
    /// let mut s = Solver::try_from(Path::new("cnfs/uf8.cnf")).expect("can't load");
    /// assert!(s.add_clause(vec![1, -2]).is_ok());
    /// assert!(s.add_clause(vec![2, -3]).is_ok());
    /// assert!(s.add_clause(vec![3, 4]).is_ok());
    /// assert!(s.add_clause(vec![-2, 4]).is_ok());
    /// assert!(s.add_clause(vec![-4, 5]).is_ok());
    /// assert!(s.add_clause(vec![-5, 6]).is_ok());
    /// assert!(s.add_clause(vec![-7, 8]).is_ok());
    /// assert!(matches!(s.add_clause(vec![10, 11]), Err(SolverError::InvalidLiteral)));
    /// assert!(matches!(s.add_clause(vec![0, 8]), Err(SolverError::InvalidLiteral)));
    /// assert_eq!(s.solve(), Ok(Certificate::UNSAT));
    ///```
    fn add_clause<V>(&'a mut self, vec: V) -> Result<&'a mut Solver<'a>, SolverError>
    where
        V: AsRef<[i32]>;
    /// add a var to solver and return the number of vars.
    ///
    /// # Example
    /// ```
    /// use crate::splr::*;
    /// use std::path::Path;
    ///
    /// let mut s = Solver::try_from(Path::new("cnfs/uf8.cnf")).expect("can't load");
    /// assert_eq!(s.asg.num_vars, 8);
    /// assert!(matches!(s.add_assignment(9), Err(SolverError::InvalidLiteral)));
    /// s.add_assignment(1).expect("panic");
    /// s.add_assignment(2).expect("panic");
    /// s.add_assignment(3).expect("panic");
    /// s.add_assignment(4).expect("panic");
    /// s.add_assignment(5).expect("panic");
    /// s.add_assignment(8).expect("panic");
    /// assert_eq!(s.add_var(), 9);
    /// assert!(s.add_assignment(-9).is_ok());
    /// assert_eq!(s.solve(), Ok(Certificate::SAT(vec![1, 2, 3, 4, 5, -6, 7, 8, -9])));
    /// ```
    fn add_var(&'a mut self) -> VarId;
    #[cfg(not(feature = "no_IO"))]
    /// make a solver and load a CNF into it.
    ///
    /// # Errors
    ///
    /// * `SolverError::IOError` if it failed to load a CNF file.
    /// * `SolverError::Inconsistent` if the CNF is conflicting.
    /// * `SolverError::InvalidLiteral` if any literal used in the CNF is out of range for var index.
    fn build(config: &Config) -> Result<Solver<'static>, SolverError>;
    #[cfg(not(feature = "no_IO"))]
    /// dump an UNSAT certification file
    fn save_certification(&mut self);
    #[cfg(not(feature = "no_IO"))]
    /// dump the current status as a CNF
    fn dump_cnf(&self, fname: &Path);
}

impl Instantiate for Solver<'_> {
    /// ```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use splr::solver::Solver;
    /// let s = Solver::instantiate(&Config::default(), &CNFDescription::default());
    ///```
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Solver<'static> {
        Solver {
            vars: Var::new_vars(cnf.num_of_variables),
            vam: VarActivityManager::default(),
            asg: AssignStack::instantiate(config, cnf),
            cdb: ClauseDB::instantiate(config, cnf),
            state: State::instantiate(config, cnf),
        }
    }
}

/// Example
///```
/// use crate::splr::*;
///
/// let v: Vec<Vec<i32>> = vec![];
/// assert!(matches!(
///     Solver::try_from((Config::default(), v.as_ref())),
///     Ok(_)
/// ));
/// assert!(matches!(
///     Solver::try_from((Config::default(), vec![vec![0_i32]].as_ref())),
///     Err(Err(SolverError::InvalidLiteral))
/// ));
///```
impl<V> TryFrom<(Config, &[V])> for Solver<'_>
where
    V: AsRef<[i32]>,
{
    type Error = SolverResult;
    fn try_from((config, vec): (Config, &[V])) -> Result<Self, Self::Error> {
        let cnf = CNFDescription::from(vec);
        match Solver::instantiate(&config, &cnf).inject_from_vec(vec) {
            Err(SolverError::RootLevelConflict) => Err(Ok(Certificate::UNSAT)),
            Err(e) => Err(Err(e)),
            Ok(s) => Ok(s),
        }
    }
}

#[cfg(not(feature = "no_IO"))]
impl TryFrom<&Path> for Solver<'_> {
    type Error = SolverError;
    /// return a new solver build for a CNF file.
    ///
    /// # Example
    /// ```
    /// use crate::splr::solver::{SatSolverIF, Solver};
    /// use std::path::Path;
    ///
    /// let mut s = Solver::try_from(Path::new("cnfs/sample.cnf")).expect("fail to load");
    ///```
    fn try_from(s: &Path) -> Result<Self, Self::Error> {
        let config = Config::from(s);
        Solver::build(&config)
    }
}

impl<'a> SatSolverIF<'a> for Solver<'a> {
    fn add_assignment(&'a mut self, val: i32) -> Result<&'a mut Solver<'a>, SolverError> {
        // let Solver {
        //     ref mut vars,
        //     ref mut asg,
        //     ref mut vam,
        //     ref mut cdb,
        //     ..
        // } = self;
        let vars: &'a mut Vec<Var<'a>> = &mut self.vars;
        let asg: &'a mut AssignStack<'a> = &mut self.asg;
        let vam: &'a mut VarActivityManager = &mut self.vam;
        let cdb: &'a mut ClauseDB<'a> = &mut self.cdb;
        if val == 0 || asg.num_vars < val.unsigned_abs() as usize {
            return Err(SolverError::InvalidLiteral);
        }
        let v: &'a Var<'a> = &vars[val.unsigned_abs() as usize];
        let vc = v.clone();
        let vr: &'a Var<'a> = &vc;
        let lit: Lit<'a> = Lit::from((vr, val < 0));
        cdb.certificate_add_assertion(lit);
        let v: &'a mut Var<'a> = &mut vars[val.unsigned_abs() as usize];
        match lit.assigned() {
            None => assign_at_root_level(asg, vam, lit, v).map(|_| self),
            Some(true) => Ok(self),
            Some(false) => Err(SolverError::RootLevelConflict),
        }
    }
    fn add_clause<V>(&mut self, vec: V) -> Result<&mut Solver<'a>, SolverError>
    where
        V: AsRef<[i32]>,
    {
        for i in vec.as_ref().iter() {
            if *i == 0 || self.asg.num_vars < i.unsigned_abs() as usize {
                return Err(SolverError::InvalidLiteral);
            }
        }
        let mut clause = vec
            .as_ref()
            .iter()
            .map(|i| Lit::from((&self.vars[i.unsigned_abs() as usize], *i < 0)))
            .collect::<Vec<Lit>>();

        if clause.is_empty() {
            return Err(SolverError::EmptyClause);
        }
        if self.add_unchecked_clause(&mut clause) == RefClause::EmptyClause {
            return Err(SolverError::EmptyClause);
        }
        Ok(self)
    }
    fn add_var(&mut self) -> VarId {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut state,
            ..
        } = self;
        asg.handle(SolverEvent::NewVar);
        cdb.handle(SolverEvent::NewVar);
        state.handle(SolverEvent::NewVar);
        asg.num_vars as VarId
    }
    /// # Examples
    ///
    /// ```
    /// use splr::config::Config;
    /// use splr::solver::{SatSolverIF, Solver};
    ///
    /// let config = Config::from("cnfs/sample.cnf");
    /// assert!(Solver::build(&config).is_ok());
    ///```
    #[cfg(not(feature = "no_IO"))]
    fn build(config: &Config) -> Result<Solver<'static>, SolverError> {
        let CNFReader { cnf, reader } = CNFReader::try_from(Path::new(&config.cnf_file))?;
        Solver::instantiate(config, &cnf).inject(reader)
    }
    #[cfg(not(feature = "no_IO"))]
    /// dump an UNSAT certification file
    fn save_certification(&mut self) {
        self.cdb.certificate_save();
    }
    #[cfg(not(feature = "no_IO"))]
    /// dump all active clauses and assertions as a CNF file.
    fn dump_cnf(&self, fname: &Path) {
        let Solver { asg, cdb, .. } = self;
        cdb.dump_cnf(asg, fname)
    }
}

impl<'a> Solver<'a> {
    // renamed from clause_new
    fn add_unchecked_clause(&mut self, lits: &mut Vec<Lit>) -> RefClause {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ..
        } = self;
        if lits.is_empty() {
            return RefClause::EmptyClause;
        }
        debug_assert!(asg.decision_level() == 0);
        lits.sort();
        let mut j = 0;
        let mut l_: Option<Lit> = None; // last literal; [x, x.negate()] means tautology.
        for i in 0..lits.len() {
            let li = lits[i];
            let sat = li.assigned();
            if sat == Some(true) || Some(!li) == l_ {
                return RefClause::Dead;
            } else if sat != Some(false) && Some(li) != l_ {
                lits[j] = li;
                j += 1;
                l_ = Some(li);
            }
        }
        lits.truncate(j);
        match lits.len() {
            0 => RefClause::EmptyClause, // for UNSAT
            1 => {
                let l0 = lits[0];
                cdb.certificate_add_assertion(l0);
                asg.assign_at_root_level(l0)
                    .map_or(RefClause::EmptyClause, |_| RefClause::UnitClause(l0))
            }
            _ => cdb.new_clause(lits, false),
        }
    }
    #[cfg(not(feature = "no_IO"))]
    fn inject(mut self, mut reader: BufReader<File>) -> Result<Solver<'a>, SolverError> {
        self.state.progress_header();
        self.state.progress(&self.asg, &self.cdb);
        self.state.flush("Initialization phase: loading...");
        let mut buf = String::new();
        loop {
            buf.clear();
            let mut ends_zero = false;
            match reader.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_) if buf.starts_with('c') => continue,
                Ok(_) => {
                    let iter = buf.split_whitespace();
                    let mut v: Vec<Lit> = Vec::new();
                    for s in iter {
                        match s.parse::<i32>() {
                            Ok(0) => {
                                ends_zero = true;
                                break;
                            }
                            Ok(val) => v.push(Lit::from((
                                &self.vars[val.unsigned_abs() as usize],
                                val < 0,
                            ))),
                            Err(_) => (),
                        }
                    }
                    if v.is_empty() {
                        if ends_zero {
                            return Err(SolverError::EmptyClause);
                        }
                        continue;
                    } else if self.add_unchecked_clause(&mut v) == RefClause::EmptyClause {
                        return Err(SolverError::EmptyClause);
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(self.asg.num_vars, self.state.target.num_of_variables);
        // s.state[Stat::NumBin] = s.cdb.iter().skip(1).filter(|c| c.len() == 2).count();
        Ok(self)
    }
    fn inject_from_vec<V>(mut self, v: &[V]) -> Result<Solver<'a>, SolverError>
    where
        V: AsRef<[i32]>,
    {
        self.state.progress_header();
        self.state.progress(&self.asg, &self.cdb);
        self.state.flush("injecting...");
        for ints in v.iter() {
            for i in ints.as_ref().iter() {
                if *i == 0 || self.asg.num_vars < i.unsigned_abs() as usize {
                    return Err(SolverError::InvalidLiteral);
                }
            }
            let mut lits: Vec<Lit<'a>> = ints
                .as_ref()
                .iter()
                .map(|i| Lit::from((&self.vars[i.unsigned_abs() as usize], *i < 0)))
                .collect::<Vec<Lit<'a>>>();
            if v.is_empty() {
                return Err(SolverError::EmptyClause);
            }
            if self.add_unchecked_clause(&mut lits) == RefClause::EmptyClause {
                return Err(SolverError::EmptyClause);
            }
        }
        debug_assert_eq!(self.asg.num_vars, self.state.target.num_of_variables);
        // s.state[Stat::NumBin] = s.cdb.iter().skip(1).filter(|c| c.len() == 2).count();
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    // use super::*;
    use crate::*;
    use std::path::Path;

    #[cfg(not(feature = "no_IO"))]
    #[test]
    fn test_add_var() {
        let mut s = Solver::try_from(Path::new("cnfs/uf8.cnf")).expect("can't load");
        assert_eq!(s.asg.num_vars, 8);
        assert!(matches!(
            s.add_assignment(9),
            Err(SolverError::InvalidLiteral)
        ));
        s.add_assignment(1).expect("panic");
        s.add_assignment(2).expect("panic");
        s.add_assignment(3).expect("panic");
        s.add_assignment(4).expect("panic");
        s.add_assignment(5).expect("panic");
        s.add_assignment(8).expect("panic");
        assert_eq!(s.add_var(), 9);
        // assert!(s.add_assignment(-9).is_ok());
        s.add_clause([-1, -8, -9]).expect("panic");
        assert_eq!(
            s.solve(),
            Ok(Certificate::SAT(vec![1, 2, 3, 4, 5, -6, 7, 8, -9]))
        );
    }
}

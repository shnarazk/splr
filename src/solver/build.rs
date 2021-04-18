//! Solver Builder
use {
    super::{restart::Restarter, Certificate, Solver, SolverEvent, SolverResult, State, StateIF},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        processor::{EliminateIF, Eliminator},
        types::*,
    },
    std::convert::TryFrom,
};

#[cfg(not(feature = "no_IO"))]
use std::{
    fs::File,
    io::{BufRead, BufReader, Write},
};

/// API for SAT solver creation and modification.
pub trait SatSolverIF: Instantiate {
    /// add an assignment to Solver.
    ///
    /// # Errors
    ///
    /// * `SolverError::Inconsistent` if it conflicts with existing assignments.
    /// * `SolverError::OutOfRange` if it is out of range for var index.
    ///
    /// # Example
    ///
    /// ```
    /// use crate::splr::*;
    /// use std::convert::TryFrom;
    /// use crate::splr::assign::VarManipulateIF;    // for s.asg.assign()
    ///
    /// let mut s = Solver::try_from("cnfs/uf8.cnf").expect("can't load");
    /// assert!(s.add_assignment(1).is_ok());
    /// assert_eq!(s.asg.assign(1), Some(true));
    /// assert!(s.add_assignment(2).is_ok());
    /// assert!(s.add_assignment(3).is_ok());
    /// assert!(s.add_assignment(4).is_ok());
    /// assert!(s.add_assignment(5).is_ok());
    /// assert!(s.add_assignment(8).is_ok());
    /// assert!(matches!(s.add_assignment(-1), Err(SolverError::Inconsistent)));
    /// assert!(matches!(s.add_assignment(10), Err(SolverError::OutOfRange)));
    /// assert!(matches!(s.add_assignment(0), Err(SolverError::OutOfRange)));
    /// assert_eq!(s.solve(), Ok(Certificate::SAT(vec![1, 2, 3, 4, 5, -6, 7, 8])));
    /// ```
    fn add_assignment(&mut self, val: i32) -> Result<&mut Solver, SolverError>;
    /// add a literal to Solver.
    ///
    /// # Errors
    ///
    /// * `SolverError::Inconsistent` if a given clause is unit and conflicts with existing assignments.
    /// * `SolverError::OutOfRange` if a literal in it is out of range for var index.
    ///
    /// # Example
    ///```
    /// use crate::splr::*;
    /// use std::convert::TryFrom;
    ///
    /// let mut s = Solver::try_from("cnfs/uf8.cnf").expect("can't load");
    /// assert!(s.add_clause(vec![1, -2]).is_ok());
    /// assert!(s.add_clause(vec![2, -3]).is_ok());
    /// assert!(s.add_clause(vec![3, 4]).is_ok());
    /// assert!(s.add_clause(vec![-2, 4]).is_ok());
    /// assert!(s.add_clause(vec![-4, 5]).is_ok());
    /// assert!(s.add_clause(vec![-5, 6]).is_ok());
    /// assert!(s.add_clause(vec![-7, 8]).is_ok());
    /// assert!(matches!(s.add_clause(vec![10, 11]), Err(SolverError::OutOfRange)));
    /// assert!(matches!(s.add_clause(vec![0, 8]), Err(SolverError::OutOfRange)));
    /// assert_eq!(s.solve(), Ok(Certificate::UNSAT));
    ///```
    fn add_clause<V>(&mut self, vec: V) -> Result<&mut Solver, SolverError>
    where
        V: AsRef<[i32]>;
    /// add a var to solver and return the number of vars.
    ///
    /// # Example
    /// ```
    /// use crate::splr::*;
    /// use std::convert::TryFrom;
    ///
    /// let mut s = Solver::try_from("cnfs/uf8.cnf").expect("can't load");
    /// assert_eq!(s.asg.num_vars, 8);
    /// assert!(matches!(s.add_assignment(9), Err(SolverError::OutOfRange)));
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
    fn add_var(&mut self) -> usize;
    #[cfg(not(feature = "no_IO"))]
    /// make a solver and load a CNF into it.
    ///
    /// # Errors
    ///
    /// * `SolverError::IOError` if it failed to load a CNF file.
    /// * `SolverError::Inconsistent` if the CNF is conflicting.
    /// * `SolverError::OutOfRange` if any literal used in the CNF is out of range for var index.
    fn build(config: &Config) -> Result<Solver, SolverError>;
    /// reinitialize a solver for incremental solving. **Requires 'incremental_solver' feature**
    fn reset(&mut self);
    #[cfg(not(feature = "no_IO"))]
    /// dump an UNSAT certification file
    fn save_certification(&mut self);
    #[cfg(not(feature = "no_IO"))]
    /// dump the current status as a CNF
    fn dump_cnf(&self, fname: &str);
}

impl Default for Solver {
    fn default() -> Solver {
        Solver {
            asg: AssignStack::default(),
            cdb: ClauseDB::default(),
            elim: Eliminator::default(),
            rst: Restarter::instantiate(&Config::default(), &CNFDescription::default()),
            state: State::default(),
        }
    }
}

impl Instantiate for Solver {
    /// ```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use splr::solver::Solver;
    /// let s = Solver::instantiate(&Config::default(), &CNFDescription::default());
    ///```
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Solver {
        Solver {
            asg: AssignStack::instantiate(config, cnf),
            cdb: ClauseDB::instantiate(config, cnf),
            elim: Eliminator::instantiate(config, cnf),
            rst: Restarter::instantiate(config, &cnf),
            state: State::instantiate(config, cnf),
        }
    }
}

impl<V> TryFrom<(Config, &[V])> for Solver
where
    V: AsRef<[i32]>,
{
    type Error = SolverResult;
    fn try_from((config, vec): (Config, &[V])) -> Result<Self, Self::Error> {
        let cnf = CNFDescription::from(vec);
        match Solver::instantiate(&config, &cnf).inject_from_vec(vec) {
            Err(SolverError::Inconsistent) => Err(Ok(Certificate::UNSAT)),
            Err(e) => Err(Err(e)),
            Ok(s) => Ok(s),
        }
    }
}

#[cfg(not(feature = "no_IO"))]
impl TryFrom<&str> for Solver {
    type Error = SolverError;
    /// return a new solver build for a CNF file.
    ///
    /// # Example
    /// ```
    /// use std::convert::TryFrom;
    /// use crate::splr::solver::{SatSolverIF, Solver};
    ///
    /// let mut s = Solver::try_from("cnfs/sample.cnf").expect("fail to load");
    ///```
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let config = Config::from(s);
        Solver::build(&config)
    }
}

impl SatSolverIF for Solver {
    fn add_assignment(&mut self, val: i32) -> Result<&mut Solver, SolverError> {
        if val == 0 || self.asg.num_vars < val.abs() as usize {
            return Err(SolverError::OutOfRange);
        }
        self.asg.assign_at_root_level(Lit::from(val)).map(|_| self)
    }
    fn add_clause<V>(&mut self, vec: V) -> Result<&mut Solver, SolverError>
    where
        V: AsRef<[i32]>,
    {
        for i in vec.as_ref().iter() {
            if *i == 0 || self.asg.num_vars < i.abs() as usize {
                return Err(SolverError::OutOfRange);
            }
        }
        let mut clause = vec
            .as_ref()
            .iter()
            .map(|i| Lit::from(*i))
            .collect::<Vec<Lit>>();
        if self.add_unchecked_clause(&mut clause).is_none() {
            return Err(SolverError::Inconsistent);
        }
        Ok(self)
    }
    fn add_var(&mut self) -> usize {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut elim,
            ref mut state,
            ..
        } = self;
        asg.handle(SolverEvent::NewVar);
        cdb.handle(SolverEvent::NewVar);
        elim.handle(SolverEvent::NewVar);
        state.handle(SolverEvent::NewVar);
        asg.num_vars
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
    fn build(config: &Config) -> Result<Solver, SolverError> {
        let CNFReader { cnf, reader } = CNFReader::try_from(&config.cnf_file)?;
        Solver::instantiate(config, &cnf).inject(reader)
    }
    fn reset(&mut self) {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut elim,
            ref mut rst,
            ref mut state,
        } = self;
        asg.handle(SolverEvent::Reinitialize);
        cdb.handle(SolverEvent::Reinitialize);
        elim.handle(SolverEvent::Reinitialize);
        rst.handle(SolverEvent::Reinitialize);
        state.handle(SolverEvent::Reinitialize);

        let mut tmp = Vec::new();
        std::mem::swap(&mut tmp, &mut cdb.eliminated_permanent);
        while let Some(mut vec) = tmp.pop() {
            cdb.new_clause(asg, &mut vec, false, false);
        }
    }
    #[cfg(not(feature = "no_IO"))]
    /// dump an UNSAT certification file
    fn save_certification(&mut self) {
        self.cdb.certificate_save();
    }
    #[cfg(not(feature = "no_IO"))]
    fn dump_cnf(&self, fname: &str) {
        let nv = self.asg.derefer(crate::assign::property::Tusize::NumVar);
        for vi in 1..nv {
            if self.asg.var(vi).is(Flag::ELIMINATED) && self.asg.assign(vi).is_some() {
                panic!("conflicting var {} {:?}", vi, self.asg.assign(vi));
            }
        }
        if let Ok(out) = File::create(&fname) {
            let mut buf = std::io::BufWriter::new(out);
            let na = self
                .asg
                .derefer(crate::assign::property::Tusize::NumAssertedVar);
            let nc = self.cdb.iter().skip(1).filter(|c| !c.is_dead()).count();
            buf.write_all(format!("p cnf {} {}\n", nv, nc + na).as_bytes())
                .unwrap();
            for c in self.cdb.iter().skip(1) {
                if c.is_dead() {
                    continue;
                }
                for l in c.iter() {
                    buf.write_all(format!("{} ", i32::from(*l)).as_bytes())
                        .unwrap();
                }
                buf.write_all(b"0\n").unwrap();
            }
            buf.write_all(b"c from trail\n").unwrap();
            for x in self.asg.stack_iter().take(self.asg.len_upto(0)) {
                buf.write_all(format!("{} 0\n", i32::from(*x)).as_bytes())
                    .unwrap();
            }
        }
    }
}

impl Solver {
    /// FIXME: this should return Result<ClauseId, SolverError>
    /// fn add_unchecked_clause(&mut self, lits: &mut Vec<Lit>) -> Option<ClauseId>
    // renamed from clause_new
    fn add_unchecked_clause(&mut self, lits: &mut Vec<Lit>) -> Option<ClauseId> {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut elim,
            ..
        } = self;
        if lits.is_empty() {
            return None;
        }
        debug_assert!(asg.decision_level() == 0);
        lits.sort();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means tautology.
        for i in 0..lits.len() {
            let li = lits[i];
            let sat = asg.assigned(li);
            if sat == Some(true) || !li == l_ {
                return Some(ClauseId::default());
            } else if sat != Some(false) && li != l_ {
                lits[j] = li;
                j += 1;
                l_ = li;
            }
        }
        lits.truncate(j);
        match lits.len() {
            0 => None, // Empty clause is UNSAT.
            1 => {
                cdb.certificate_add_assertion(lits[0]);
                asg.assign_at_root_level(lits[0])
                    .map_or(None, |_| Some(ClauseId::default()))
            }
            _ => {
                let cid = cdb.new_clause(asg, lits, false, false).as_cid();
                elim.add_cid_occur(asg, cid, &mut cdb[cid], true);
                cdb[cid].rank = 1;
                Some(cid)
            }
        }
    }
    #[cfg(not(feature = "no_IO"))]
    fn inject(mut self, mut reader: BufReader<File>) -> Result<Solver, SolverError> {
        self.state.progress_header();
        self.state
            .progress(&self.asg, &self.cdb, &self.elim, &self.rst);
        self.state.flush("Initialization phase: loading...");
        let mut buf = String::new();
        loop {
            buf.clear();
            match reader.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_) if buf.starts_with('c') => continue,
                Ok(_) => {
                    let iter = buf.split_whitespace();
                    let mut v: Vec<Lit> = Vec::new();
                    for s in iter {
                        match s.parse::<i32>() {
                            Ok(0) => break,
                            Ok(val) => v.push(Lit::from(val)),
                            Err(_) => (),
                        }
                    }
                    if !v.is_empty() && self.add_unchecked_clause(&mut v).is_none() {
                        return Err(SolverError::Inconsistent);
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(self.asg.num_vars, self.state.target.num_of_variables);
        // s.state[Stat::NumBin] = s.cdb.iter().skip(1).filter(|c| c.len() == 2).count();

        #[cfg(feature = "strategy_adaptation")]
        {
            self.asg.handle(SolverEvent::Adapt(self.state.strategy, 0));
            self.rst.handle(SolverEvent::Adapt(self.state.strategy, 0));
        }

        Ok(self)
    }
    fn inject_from_vec<V>(mut self, v: &[V]) -> Result<Solver, SolverError>
    where
        V: AsRef<[i32]>,
    {
        self.state.progress_header();
        self.state
            .progress(&self.asg, &self.cdb, &self.elim, &self.rst);
        self.state.flush("injecting...");
        for ints in v.iter() {
            for i in ints.as_ref().iter() {
                if *i == 0 || self.asg.num_vars < i.abs() as usize {
                    return Err(SolverError::OutOfRange);
                }
            }
            let mut lits = ints
                .as_ref()
                .iter()
                .map(|i| Lit::from(*i))
                .collect::<Vec<Lit>>();
            if self.add_unchecked_clause(&mut lits).is_none() {
                return Err(SolverError::Inconsistent);
            }
        }
        debug_assert_eq!(self.asg.num_vars, self.state.target.num_of_variables);
        // s.state[Stat::NumBin] = s.cdb.iter().skip(1).filter(|c| c.len() == 2).count();

        #[cfg(feature = "strategy_adaptation")]
        {
            self.asg.handle(SolverEvent::Adapt(self.state.strategy, 0));
            self.rst.handle(SolverEvent::Adapt(self.state.strategy, 0));
        }

        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    // use super::*;
    use crate::*;
    use std::convert::TryFrom;

    #[cfg(not(feature = "no_IO"))]
    #[test]
    fn test_add_var() {
        let mut s = Solver::try_from("cnfs/uf8.cnf").expect("can't load");
        assert_eq!(s.asg.num_vars, 8);
        assert!(matches!(s.add_assignment(9), Err(SolverError::OutOfRange)));
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

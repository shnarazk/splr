/// Solver Builder
use {
    super::{restart::Restarter, SatSolverIF, Solver, State, StateIF},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        processor::{EliminateIF, Eliminator},
        types::*,
    },
};

#[cfg(not(features = "no_IO"))]
use std::{
    convert::TryFrom,
    fs::File,
    io::{BufRead, BufReader},
};

/// API for SAT solver like `build`, `solve` and so on.
pub trait SatSolverBuildIF {
    /// make a solver from a vec representation of a CNF.
    #[cfg(features = "no_IO")]
    fn solver_build(config: Config, vec: Vec<Vec<i32>>) -> Solver;
    /// make a solver and load a CNF into it.
    ///
    /// # Errors
    ///
    /// IO error by failing to load a CNF file.
    #[cfg(not(features = "no_IO"))]
    fn solver_build(config: &Config) -> Result<Solver, SolverError>;
    /// build a solver for solving a vec-represented CNF.
    fn solver_from_vec(config: Config, vec: Vec<Vec<i32>>) -> Solver;
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solver_add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
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

#[cfg(not(features = "no_IO"))]
impl TryFrom<&str> for Solver {
    type Error = SolverError;
    /// return a new solver build for a CNF file.
    ///
    /// # Example
    /// ```
    /// use std::convert::TryFrom;
    /// use crate::splr::solver::{SatSolverIF, Solver};
    ///
    /// let mut s = Solver::try_from("tests/sample.cnf").expect("fail to load");
    ///```
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let config = Config::from(s);
        Solver::build(&config)
    }
}

impl SatSolverBuildIF for Solver {
    fn solver_from_vec(config: Config, vec: Vec<Vec<i32>>) -> Solver {
        let cnf = CNFDescription::from(vec);
        Solver::instantiate(&config, &cnf)
    }
    /// # Examples
    ///
    /// ```
    /// use splr::config::Config;
    /// use splr::solver::{SatSolverIF, Solver};
    ///
    /// let config = Config::from("tests/sample.cnf");
    /// assert!(Solver::build(&config).is_ok());
    ///```
    #[cfg(not(features = "no_IO"))]
    fn solver_build(config: &Config) -> Result<Solver, SolverError> {
        let CNFReader { cnf, reader } = CNFReader::try_from(&config.cnf_file)?;
        Solver::instantiate(config, &cnf).inject(reader)
    }
    // renamed from clause_new
    fn solver_add_unchecked_clause(&mut self, lits: &mut Vec<Lit>) -> Option<ClauseId> {
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
        if lits.iter().any(|l| asg.assigned(*l).is_some()) {
            cdb.certificate_add(lits);
        }
        lits.sort_unstable();
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
            1 => asg
                .assign_at_rootlevel(lits[0])
                .map_or(None, |_| Some(ClauseId::default())),
            _ => {
                let cid = cdb.new_clause(asg, lits, false, false);
                elim.add_cid_occur(asg, cid, &mut cdb[cid], true);
                Some(cid)
            }
        }
    }
}

impl Solver {
    fn inject(mut self, mut reader: BufReader<File>) -> Result<Solver, SolverError> {
        self.state.progress_header();
        self.state.progress(
            &self.asg,
            &self.cdb,
            &self.elim,
            &self.rst,
            Some("initialization phase"),
        );
        self.state.flush("loading...");
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
        self.asg.adapt_to(&self.state, 0);
        self.rst.adapt_to(&self.state, 0);
        Ok(self)
    }
}

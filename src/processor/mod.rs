//!
//! * private module `eliminate` provides var elimination
//! * private module `subsume` provides clause subsumption
//!
//!# Example
//!
//!```
//!  use splr::{processor::{self, EliminateIF}, solver::Solver, types::PropertyDereference};
//!  use std::convert::TryFrom;
//!  let mut s = Solver::try_from("cnfs/sample.cnf").expect("failed to load");
//!  let Solver {
//!      ref mut asg,
//!      ref mut cdb,
//!      ref mut elim,
//!      ref mut rst,
//!      ref mut state,
//!      ..
//!  } = s;
//!  elim.activate();
//!  elim.simplify(asg, cdb, rst, state).expect("panic");
//!  assert_eq!(elim.derefer(processor::property::Tusize::NumFullElimination), 1);
//!  assert!(0 < asg.num_eliminated_vars);
//!```

mod eliminate;
mod eliminator;
mod heap;
mod subsume;

use {
    crate::{
        assign::AssignIF,
        cdb::ClauseDBIF,
        processor::heap::{LitOccurs, VarOccHeap},
        solver::restart::RestartIF,
        state::State,
        types::*,
    },
    std::slice::Iter,
};

/// API for Eliminator like `activate`, `stop`, `eliminate` and so on.
///```
/// use crate::{splr::config::Config, splr::types::*};
/// use crate::splr::processor::{Eliminator, EliminateIF};
/// use crate::splr::solver::Solver;

/// let mut s = Solver::instantiate(&Config::default(), &CNFDescription::default());
/// let elim = &mut s.elim;
/// assert_eq!(elim.is_running(), false);
/// elim.activate();
/// // At this point, the `elim` is in `ready` mode, not `running`.
/// assert_eq!(elim.is_running(), false);
/// assert_eq!(elim.simplify(&mut s.asg, &mut s.cdb, &mut s.rst, &mut s.state), Ok(()));
///```
pub trait EliminateIF: Instantiate {
    /// set eliminator's mode to **ready**.
    fn activate(&mut self);
    /// check if the eliminator is running.
    fn is_running(&self) -> bool;
    /// rebuild occur lists.
    fn prepare<A, C>(&mut self, asg: &mut A, cdb: &mut C, force: bool)
    where
        A: AssignIF,
        C: ClauseDBIF;
    /// enqueue a var into eliminator's var queue.
    fn enqueue_var<A>(&mut self, asg: &mut A, vi: VarId, upward: bool)
    where
        A: AssignIF;
    /// simplify database by:
    /// * removing satisfiable clauses
    /// * calling exhaustive simplifier that tries **clause subsumption** and **variable elimination**.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn simplify<A, C, R>(
        &mut self,
        asg: &mut A,
        cdb: &mut C,
        rst: &mut R,
        state: &mut State,
    ) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF,
        R: RestartIF;
    /// return the order of vars based on their occurrences
    fn sorted_iterator(&self) -> Iter<'_, usize>;
    /// return vi's stats
    fn stats(&self, vi: VarId) -> Option<(usize, usize)>;
    /// return the constraints on eliminated literals.
    fn eliminated_lits(&self) -> &[Lit];
}

#[derive(Copy, Clone, Eq, Debug, PartialEq)]
enum EliminatorMode {
    Dormant,
    Waiting,
    Running,
}

/// Literal eliminator
#[derive(Clone, Debug)]
pub struct Eliminator {
    enable: bool,
    pub to_simplify: f64,
    mode: EliminatorMode,
    clause_queue: Vec<ClauseId>,
    var_queue: VarOccHeap,
    bwdsub_assigns: usize,
    /// constraints on eliminated var. It is used by `extend_model`.
    elim_lits: Vec<Lit>,
    /// Maximum number of clauses to try to eliminate a var
    eliminate_var_occurrence_limit: usize,
    /// 0 for no limit
    /// Stop elimination if a generated resolvent is larger than this
    /// 0 means no limit.
    eliminate_combination_limit: f64,
    /// Stop elimination if the increase of clauses is over this
    eliminate_grow_limit: usize,
    /// A criteria by the product's of its positive occurrences and negative ones
    eliminate_occurrence_limit: usize,
    /// Stop subsumption if the size of a clause is over this
    subsume_literal_limit: usize,
    /// var
    var: Vec<LitOccurs>,
    num_full_elimination: usize,
    num_sat_elimination: usize,
    num_subsumed: usize,
}

pub mod property {
    use super::Eliminator;
    use crate::types::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Tusize {
        NumFullElimination,
        NumSatElimination,
        NumSubsumedClause,
    }

    pub const USIZES: [Tusize; 3] = [
        Tusize::NumFullElimination,
        Tusize::NumSatElimination,
        Tusize::NumSubsumedClause,
    ];

    impl PropertyDereference<Tusize, usize> for Eliminator {
        #[inline]
        fn derefer(&self, k: Tusize) -> usize {
            match k {
                Tusize::NumFullElimination => self.num_full_elimination,
                Tusize::NumSatElimination => self.num_sat_elimination,
                Tusize::NumSubsumedClause => self.num_subsumed,
            }
        }
    }
}

#[cfg(not(feature = "no_IO"))]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assign::VarManipulateIF, processor::EliminateIF, solver::Solver};
    use std::convert::TryFrom;

    #[test]
    fn check_elimination() {
        let mut config = Config::default();
        config.quiet_mode = true;
        let mut s = Solver::try_from("cnfs/sample.cnf").expect("failed to load");
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut elim,
            ref mut rst,
            ref mut state,
            ..
        } = s;
        assert!(elim.enable);
        elim.activate();
        elim.simplify(asg, cdb, rst, state).expect("");
        assert_eq!(elim.num_full_elimination, 1);
        assert!(!asg.var_iter().skip(1).all(|v| v.is(Flag::ELIMINATED)));
        assert!(0 < asg.num_eliminated_vars);
        assert_eq!(
            asg.num_eliminated_vars,
            asg.var_iter().filter(|v| v.is(Flag::ELIMINATED)).count()
        );
        let elim_vars = asg
            .var_iter()
            .filter(|v| v.is(Flag::ELIMINATED))
            .map(|v| v.index)
            .collect::<Vec<_>>();
        assert_eq!(
            0,
            cdb.iter()
                .skip(1)
                .filter(|c| !c.is_dead())
                .filter(|c| c.iter().any(|l| elim_vars.contains(&l.vi())))
                .count()
        );
    }
}

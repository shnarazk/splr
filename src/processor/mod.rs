//!
//! * private module `eliminate` provides var elimination
//! * private module `subsume` provides clause subsumption
//!
//!# Example
//!
//!```
//!  use splr::{processor::{self, Eliminator, EliminateIF}, solver::Solver, types::{Instantiate, PropertyDereference}};
//!  use std::path::Path;
//!
//!  let mut s = Solver::try_from(Path::new("cnfs/sample.cnf")).expect("failed to load");
//!  let Solver {
//!      ref mut asg,
//!      ref mut cdb,
//!      ref mut state,
//!      ..
//!  } = s;
//!  let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
//!  elim.simplify(asg, cdb, state, false).expect("panic");
//!  assert!(!state.config.enable_eliminator || 0 < asg.num_eliminated_vars);
//!```

mod eliminate;
mod heap;
mod simplify;
mod subsume;

use {
    crate::{
        assign::AssignIF,
        cdb::ClauseDBIF,
        processor::heap::{LitOccurs, VarOccHeap},
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
///
/// let mut s = Solver::instantiate(&Config::default(), &CNFDescription::default());
/// let mut elim = Eliminator::instantiate(&s.state.config, &s.state.cnf);
/// assert_eq!(elim.is_running(), false);
/// assert_eq!(elim.simplify(&mut s.asg, &mut s.cdb, &mut s.state, false), Ok(()));
///```
pub trait EliminateIF: Instantiate {
    /// check if the eliminator is running.
    fn is_running(&self) -> bool;
    /// rebuild occur lists.
    fn prepare(&mut self, asg: &mut impl AssignIF, cdb: &mut impl ClauseDBIF, force: bool);
    /// enqueue a var into eliminator's var queue.
    fn enqueue_var(&mut self, vi: VarId, upward: bool);
    /// simplify database by:
    /// * removing satisfiable clauses
    /// * calling exhaustive simplifier that tries **clause subsumption** and **variable elimination**.
    ///
    /// Note: `force_run` is used only at the beginning of `solve' for simple satisfiability check
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn simplify(
        &mut self,
        asg: &mut impl AssignIF,
        cdb: &mut impl ClauseDBIF,
        state: &mut State,
        force_run: bool,
    ) -> MaybeInconsistent;
    /// return the order of vars based on their occurrences
    fn sorted_iterator(&self) -> Iter<'_, u32>;
    /// return vi's stats
    fn stats(&self, vi: VarId) -> Option<(usize, usize)>;
    /// return the constraints on eliminated literals.
    fn eliminated_lits(&mut self) -> &mut Vec<Lit>;
}

#[derive(Copy, Clone, Eq, Debug, PartialEq)]
enum EliminatorMode {
    Dormant,
    Running,
}

/// Literal eliminator
#[derive(Clone, Debug)]
pub struct Eliminator {
    enable: bool,
    mode: EliminatorMode,
    clause_queue: Vec<ClauseId>,
    var_queue: VarOccHeap,
    bwdsub_assigns: usize,
    /// constraints on eliminated var. It is used by `extend_model`.
    elim_lits: Vec<Lit>,
    /// Maximum number of clauses to try to eliminate a var
    eliminate_var_occurrence_limit: usize,
    /// Stop elimination if the increase of clauses is over this
    eliminate_grow_limit: usize,
    /// A criteria by the product's of its positive occurrences and negative ones
    eliminate_occurrence_limit: usize,
    /// Stop subsumption if the size of a clause is over this
    subsume_literal_limit: usize,
    /// var
    var: Vec<LitOccurs>,
    pub num_subsumed: usize,
}

#[cfg(not(feature = "no_IO"))]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{solver::Solver, var_vector::*};
    use std::path::Path;

    #[test]
    fn check_elimination() {
        let mut config = Config::default();
        if !config.enable_eliminator {
            return;
        }
        config.quiet_mode = true;
        let mut s = Solver::try_from(Path::new("cnfs/sample.cnf")).expect("failed to load");
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut state,
            ..
        } = s;
        let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
        assert!(elim.enable);
        elim.simplify(asg, cdb, state, false).expect("");
        assert!(!VarRef::var_id_iter().all(|vi| VarRef(vi).is(FlagVar::ELIMINATED)));
        assert!(0 < asg.num_eliminated_vars);
        assert_eq!(
            asg.num_eliminated_vars,
            VarRef::var_id_iter()
                .filter(|vi| VarRef(*vi).is(FlagVar::ELIMINATED))
                .count()
        );
        let elim_vars = VarRef::var_id_iter()
            .filter(|vi| VarRef(*vi).is(FlagVar::ELIMINATED))
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

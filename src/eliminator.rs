#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
use types::*;
use var::*;
use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause_manage::ClauseManagement;
use solver::{Solver, Stat};

/// Literal eliminator
struct Eliminator {
    heap: VarIndexHeap,
    n_touched: usize,
    n_occ: Vec<Lit>,
    occurs: Vec<(Var, ClauseId, bool)>,
    subsumption_queue: Vec<ClauseId>,
    // frozen: Vec<Var>,           // should be in Var
    // eliminated: Vec<Var>,       // should be in VarIndexHeap
    bwdsub_assigns: usize,
    bwdsub_tmpunit: ClauseId,
}

trait LiteralEliminator {
    fn asymm () -> bool;
    fn asymm_var () -> bool;
    fn update_elim_heap();
    fn gather_toched_clauses();
    fn merge(&self) -> bool;
    fn backward_subsumption_check() -> bool;
    fn eliminate_var(&self, vi: VarIndex) -> bool;
    fn extend_model(&self) -> ();
    fn remove_clause(&self, cid: ClauseId) -> ();
    fn strengthen_clause(&self, cid: ClauseId) -> bool;
    fn cleaup_clauses(&self) -> ();
    fn implied(&self, vec: &[Lit]) -> bool;
}

impl Solver {
    fn func1(&self) -> Lbool {
        let extra = Vec::new();
        for l in &self.assumption {
            let v = &mut self.vars[l.vi()];
            if !v.frozen {
                v.frozen = true;
                extra.push(l.vi());
            }
        }
        let result = self.eliminate(false);
        if result == LTRUE {
            result = self.solve();
        }
        if result == LTRUE {
            result = self.extend_model();
        }
        for vi in &extra {
            self.vars[vi].frozen = false;
        }
        result
   }
}

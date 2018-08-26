#![allow(dead_code)]
use solver::{Solver, Stat};
use types::*;
use var::Var;
use var::VarOrdering;
use var::VarIndexHeap;
use solver::SatSolver;

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;

pub trait VarSelect {
    fn select_var(&mut self) -> VarIndex;
    fn bump_vi(&mut self, vi: VarIndex) -> ();
    fn decay_var_activity(&mut self) -> ();
    fn rebuild_vh(&mut self) -> ();
}

impl VarSelect for Solver {
    fn rebuild_vh(&mut self) -> () {
        if self.decision_level() != 0 {
            return;
        }
        self.var_order.reset();
        for vi in 1..self.vars.len() {
            if self.vars[vi].assign == BOTTOM {
                self.var_order.insert(&self.vars, vi);
            }
        }
    }
    fn bump_vi(&mut self, vi: VarIndex) -> () {
        let d = self.stats[Stat::NumOfBackjump as usize] as f64;
        let a = (self.vars[vi].activity + d) / 2.0;
        self.vars[vi].activity = a;
        if VAR_ACTIVITY_THRESHOLD < a {
            // self.rescale_var_activity();
            for i in 1..self.vars.len() {
                self.vars[i].activity = self.vars[i].activity / VAR_ACTIVITY_THRESHOLD;
            }
            self.var_inc /= VAR_ACTIVITY_THRESHOLD;
        }
        self.var_order.update(&self.vars, vi);
    }
    fn decay_var_activity(&mut self) -> () {
        self.var_inc = self.var_inc / VAR_ACTIVITY_THRESHOLD;
    }
    /// Heap operations; renamed from selectVO
    fn select_var(&mut self) -> VarIndex {
        loop {
            if self.var_order.len() == 0 {
                return 0;
            }
            let vi = self.var_order.root(&self.vars);
            let x = self.vars[vi].assign;
            if x == BOTTOM {
                return vi;
            }
        }
    }
}

/// Literal eliminator
pub struct Eliminator {
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
    fn func2(&mut self) -> Lbool {
        let mut extra = Vec::new();
        for vi in &self.assumption {
            let v = &mut self.vars[*vi as usize];
            if !v.frozen {
                v.frozen = true;
                extra.push(*vi);
            }
        }
        let result = self.eliminate(false);
        if result == LTRUE {
            match self.solve() {
                Ok(_) => self.extend_model(),
                _ => (),
            }
        }
        for vi in &extra {
            self.vars[*vi as usize].frozen = false;
        }
        result
    }
    pub fn eliminate(&self, _:bool) -> Lbool {
        LTRUE
    }
    pub fn extend_model(&self) -> () {
    }
}

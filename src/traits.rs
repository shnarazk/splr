use crate::assign::AssignStack;
use crate::clause::{Clause, ClauseDB, ClauseFlag, ClauseIndex};
use crate::config::SolverConfig;
use crate::eliminator::Eliminator;
use crate::solver::{Solver, SolverResult};
use crate::state::SolverState;
use crate::types::{CNFDescription, ClauseId, Lbool, Lit, VarId};
use crate::var::{Var, VarIdHeap};

pub trait AssignIF {
    fn new(n: usize) -> Self;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn level(&self) -> usize;
    fn is_zero(&self) -> bool;
    fn num_at(&self, n: usize) -> usize;
    fn sweep(&mut self) -> Lit;
    fn catchup(&mut self);
    fn remains(&self) -> bool;
    fn level_up(&mut self);
    fn cancel_until(&mut self, vars: &mut [Var], var_order: &mut VarIdHeap, lv: usize);
    fn enqueue(&mut self, v: &mut Var, sig: Lbool, cid: ClauseId, dl: usize) -> bool;
    fn enqueue_null(&mut self, v: &mut Var, sig: Lbool, dl: usize) -> bool;
    fn uncheck_enqueue(&mut self, vars: &mut [Var], l: Lit, cid: ClauseId);
    fn uncheck_assume(&mut self, vars: &mut [Var], elim: &mut Eliminator, l: Lit);
    fn dump_cnf(&mut self, config: &SolverConfig, cdb: &ClauseDB, vars: &[Var], fname: &str);
}

pub trait ClauseIF {
    fn get_flag(&self, flag: ClauseFlag) -> bool;
    fn flag_off(&mut self, flag: ClauseFlag);
    fn flag_on(&mut self, flag: ClauseFlag);
}

/// For ClauseDB
pub trait ClauseDBIF {
    fn new(nv: usize, nc: usize) -> Self;
    fn add_clause(
        &mut self,
        config: &mut SolverConfig,
        elim: &mut Eliminator,
        vars: &mut [Var],
        v: &mut Vec<Lit>,
        lbd: usize,
    ) -> ClauseId;
    fn remove_clause(&mut self, cid: ClauseId);
    fn reduce(&mut self, elim: &mut Eliminator, state: &mut SolverState, vars: &mut [Var]);
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut SolverConfig,
        elim: &mut Eliminator,
        state: &mut SolverState,
        vars: &mut [Var],
    ) -> bool;
    fn garbage_collect(&mut self, vars: &mut [Var], elim: &mut Eliminator);
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool) -> ClauseId;
    fn reset_lbd(&mut self, vars: &[Var], temp: &mut [usize]);
    fn bump_activity(&mut self, inc: &mut f64, cid: ClauseIndex, _d: f64);
    fn count(&self, alive: bool) -> usize;
}

pub trait ClauseIdIF {
    fn to_lit(self) -> Lit;
    fn is_lifted_lit(self) -> bool;
    fn format(self) -> String;
}

pub trait Delete<T> {
    fn delete_stable<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
    fn delete_unstable<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
}

pub trait EliminatorIF {
    fn new(use_elim: bool) -> Eliminator;
    fn stop(&mut self, cdb: &mut ClauseDB, vars: &mut [Var], force: bool);
    fn enqueue_clause(&mut self, cid: ClauseId, ch: &mut Clause);
    fn clear_clause_queue(&mut self, cdb: &mut ClauseDB);
    fn clause_queue_len(&self) -> usize;
    fn enqueue_var(&mut self, v: &mut Var);
    fn clear_var_queue(&mut self, vars: &mut [Var]);
    fn var_queue_len(&self) -> usize;
    fn eliminate(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut SolverConfig,
        cdb: &mut ClauseDB,
        state: &mut SolverState,
        vars: &mut [Var],
    );
    fn extend_model(&mut self, model: &mut Vec<i32>);
}

pub trait EmaIF {
    fn new(f: usize) -> Self;
    fn get(&self) -> f64;
    fn reset(&mut self) {}
    fn update(&mut self, x: f64);
}

pub trait LitIF {
    /// converts to var index
    fn vi(&self) -> VarId;
    fn int(&self) -> i32;
    fn lbool(&self) -> Lbool;
    fn positive(&self) -> bool;
    fn negate(&self) -> Lit;
    fn to_cid(self) -> ClauseId;
}

pub trait Propagate {
    fn propagate(
        &mut self,
        cdb: &mut ClauseDB,
        state: &mut SolverState,
        vars: &mut [Var],
    ) -> ClauseId;
}

pub trait RestartIF {
    fn block_restart(&mut self, asgs: &AssignStack, config: &SolverConfig, ncnfl: usize) -> bool;
    fn force_restart(&mut self, config: &mut SolverConfig, ncnfl: &mut f64) -> bool;
    fn restart_update_lbd(&mut self, lbd: usize);
    fn restart_update_asg(&mut self, config: &SolverConfig, n: usize);
    fn restart_update_luby(&mut self, config: &mut SolverConfig);
}

pub trait SatSolver {
    fn build(config: SolverConfig, path: &str) -> (Solver, CNFDescription);
    fn solve(&mut self) -> SolverResult;
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

pub trait SolverStateIF {
    fn new(config: &SolverConfig, nv: usize, se: i32, fname: &str) -> SolverState;
    fn progress(
        &mut self,
        config: &mut SolverConfig,
        cdb: &ClauseDB,
        elim: &Eliminator,
        vars: &[Var],
        mes: Option<&str>,
    );
    fn dump(&self, asgs: &AssignStack, str: &str);
}

pub trait VarIF {
    fn new(i: usize) -> Var;
    fn new_vars(n: usize) -> Vec<Var>;
}

pub trait VarIdIF {
    fn lit(&self, p: Lbool) -> Lit;
}

pub trait VarDBIF {
    fn assigned(&self, l: Lit) -> Lbool;
    fn locked(&self, ch: &Clause, cid: ClauseId) -> bool;
    fn satisfies(&self, c: &[Lit]) -> bool;
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize;
    fn attach_clause(
        &mut self,
        elim: &mut Eliminator,
        cid: ClauseId,
        ch: &mut Clause,
        enqueue: bool,
    );
    fn detach_clause(&mut self, elim: &mut Eliminator, cid: ClauseId, ch: &Clause);
    fn bump_activity(&mut self, inc: &mut f64, vi: VarId, _d: f64);
}

pub trait VarOrderIF {
    fn new(n: usize, init: usize) -> VarIdHeap;
    fn update(&mut self, vec: &[Var], v: VarId);
    fn insert(&mut self, vec: &[Var], vi: VarId);
    fn clear(&mut self);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn select_var(&mut self, vars: &[Var]) -> VarId;
    fn rebuild(&mut self, vars: &[Var]);
}

pub trait WatchDBIF {
    fn initialize(self, n: usize) -> Self;
    fn count(&self) -> usize;
    fn attach(&mut self, blocker: Lit, c: usize);
    fn detach(&mut self, n: usize);
    fn detach_with(&mut self, cid: usize);
}

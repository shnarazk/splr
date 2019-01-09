use crate::assign::AssignStack;
use crate::clause::{Clause, ClauseDB, ClauseFlag, ClauseIndex, ClauseKind, ClausePartition};
use crate::config::SolverConfig;
use crate::eliminator::Eliminator;
use crate::solver::{Solver, SolverResult};
use crate::state::SolverState;
use crate::types::{CNFDescription, ClauseId, Lbool, Lit, VarId};
use crate::var::{Var, VarIdHeap};

pub trait AssignIF {
    fn new(n: usize) -> AssignStack;
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
    fn dump_cnf(&mut self, config: &SolverConfig, cps: &ClauseDB, vars: &[Var], fname: &str);
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
        act: f64,
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
}

pub trait ClauseKindIF {
    fn id_from(self, cix: ClauseIndex) -> ClauseId;
}

pub trait ClauseIdIF {
    fn to_index(&self) -> ClauseIndex;
    fn to_kind(&self) -> usize;
    fn is(&self, kind: ClauseKind, ix: ClauseIndex) -> bool;
    fn fmt(&self) -> String;
}

pub trait ClausePartitionIF {
    fn build(kind: ClauseKind, nv: usize, nc: usize) -> ClausePartition;
    fn garbage_collect(&mut self, vars: &mut [Var], elim: &mut Eliminator);
    fn new_clause(&mut self, v: &[Lit], rank: usize) -> ClauseId;
    fn reset_lbd(&mut self, vars: &[Var], temp: &mut [usize]);
    fn bump_activity(&mut self, inc: &mut f64, cix: ClauseIndex, _d: f64);
    fn count(&self, alive: bool) -> usize;
}

pub trait Delete<T> {
    fn delete<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
    fn delete_unstable<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
}

pub trait EliminatorIF {
    fn new(use_elim: bool) -> Eliminator;
    fn enqueue_clause(&mut self, cid: ClauseId, ch: &mut Clause);
    fn enqueue_var(&mut self, v: &mut Var);
    fn clause_queue_len(&self) -> usize;
    fn var_queue_len(&self) -> usize;
    fn eliminate(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut SolverConfig,
        cps: &mut ClauseDB,
        state: &mut SolverState,
        vars: &mut [Var],
    );
    fn extend_model(&mut self, model: &mut Vec<i32>);
}

pub trait EmaIF {
    /// returns an EMA value
    fn get(&self) -> f64;
    fn update(&mut self, x: f64);
    /// reset (equalize) both values
    fn reset(&mut self);
}

pub trait LitIF {
    /// converts to var index
    fn vi(&self) -> VarId;
    fn int(&self) -> i32;
    fn lbool(&self) -> Lbool;
    fn positive(&self) -> bool;
    fn negate(&self) -> Lit;
    fn as_uniclause(self) -> ClauseId;
}

pub trait Propagate {
    fn propagate(
        &mut self,
        cp: &mut ClauseDB,
        state: &mut SolverState,
        vars: &mut [Var],
    ) -> ClauseId;
}

/// For VecDeque<usize>
pub trait QueueOperations {
    fn average(&self) -> f64;
    fn enqueue(&mut self, lim: usize, x: usize) -> bool;
    fn is_full(&self, lim: usize) -> bool;
}

pub trait RestartIF {
    fn block_restart(&mut self, asgs: &AssignStack, config: &SolverConfig, ncnfl: usize) -> bool;
    fn force_restart(&mut self, config: &mut SolverConfig, ncnfl: &mut f64) -> bool;
    fn restart_update_lbd(&mut self, lbd: usize);
    fn restart_update_asg(&mut self, n: usize);
    fn restart_update_luby(&mut self, config: &mut SolverConfig);
}

pub trait SatSolver {
    fn build(path: &str) -> (Solver, CNFDescription);
    fn solve(&mut self) -> SolverResult;
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

pub trait SolverStateIF {
    fn new(nv: usize, se: i32, fname: &str) -> SolverState;
    // print a progress report
    fn progress(
        &mut self,
        asgs: &AssignStack,
        config: &mut SolverConfig,
        cp: &ClauseDB,
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
    /// converter from [VarId](type.VarId.html) to [Lit](type.Lit.html).
    /// returns a positive literal if p == LTRUE or BOTTOM.
    fn lit(&self, p: Lbool) -> Lit;
}

/// For [Var]
pub trait VarManagement {
    fn assigned(&self, l: Lit) -> Lbool;
    fn locked(&self, ch: &Clause, cid: ClauseId) -> bool;
    fn satisfies(&self, c: &[Lit]) -> bool;
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize;
    fn attach_clause(
        &mut self,
        elim: &mut Eliminator,
        cid: ClauseId,
        ch: &mut Clause,
        ignorable: bool,
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

/// For Vec<Watch>
pub trait WatchManagement {
    fn initialize(self, n: usize) -> Self;
    fn count(&self) -> usize;
    fn attach(&mut self, blocker: Lit, c: usize);
    fn detach(&mut self, n: usize);
    fn detach_with(&mut self, cix: usize);
}

use crate::assign::AssignStack;
use crate::clause::*;
use crate::config::SolverConfiguration;
use crate::eliminator::Eliminator;
use crate::solver::{Solver, SolverResult};
use crate::state::SolverState;
use crate::types::*;
use crate::var::{Var, VarIdHeap};

pub trait AssignIF {
    fn new(n: usize) -> AssignStack;
    fn push(&mut self, l: Lit);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn level(&self) -> usize;
    fn is_zero(&self) -> bool;
    fn num_at(&self, n: usize) -> usize;
    fn sweep(&mut self) -> Lit;
    fn catchup(&mut self);
    fn remains(&self) -> bool;
    fn level_up(&mut self);
    fn enqueue(&mut self, v: &mut Var, sig: Lbool, cid: ClauseId, dl: usize) -> bool;
    fn enqueue_null(&mut self, v: &mut Var, sig: Lbool, dl: usize) -> bool;
    fn cancel_until(&mut self, vars: &mut [Var], var_order: &mut VarIdHeap, lv: usize);
    fn uncheck_enqueue(&mut self, vars: &mut [Var], l: Lit, cid: ClauseId);
    fn uncheck_assume(&mut self, vars: &mut [Var], eliminator: &mut Eliminator, l: Lit);
    fn dump_cnf(&mut self, config: &SolverConfiguration, cps: &ClauseDB, vars: &[Var], fname: &str);
}

pub trait ClauseIF {
    fn get_kind(&self) -> ClauseKind;
    fn flag_off(&mut self, flag: ClauseFlag);
    fn flag_on(&mut self, flag: ClauseFlag);
    fn set_flag(&mut self, flag: ClauseFlag, val: bool);
    fn get_flag(&self, flag: ClauseFlag) -> bool;
}

/// For ClauseDB
pub trait ClauseDBIF {
    fn add_clause(
        &mut self,
        config: &mut SolverConfiguration,
        elim: &mut Eliminator,
        vars: &mut [Var],
        v: &mut Vec<Lit>,
        lbd: usize,
        act: f64,
    ) -> ClauseId;
    fn remove_clause(&mut self, cid: ClauseId);
    fn change_clause_kind(
        &mut self,
        elim: &mut Eliminator,
        vars: &mut [Var],
        cid: ClauseId,
        kind: ClauseKind,
    );
    fn reduce(&mut self, elim: &mut Eliminator, state: &mut SolverState, vars: &mut [Var]);
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut SolverConfiguration,
        elim: &mut Eliminator,
        state: &mut SolverState,
        vars: &mut [Var],
    ) -> bool;
}

pub trait ClauseKindIF {
    fn tag(self) -> usize;
    fn mask(self) -> usize;
    fn id_from(self, cix: ClauseIndex) -> ClauseId;
    fn index_from(self, cid: ClauseId) -> ClauseIndex;
}

pub trait ClausePartitionIF {
    fn build(kind: ClauseKind, nv: usize, nc: usize) -> ClausePartition;
    fn id_from(&self, cix: ClauseIndex) -> ClauseId;
    fn index_from(&self, cid: ClauseId) -> ClauseIndex;
    fn garbage_collect(&mut self, vars: &mut [Var], elim: &mut Eliminator);
    fn new_clause(&mut self, v: &[Lit], rank: usize) -> ClauseId;
    fn reset_lbd(&mut self, vars: &[Var], temp: &mut [usize]);
    fn bump_activity(&mut self, cix: ClauseIndex, val: f64, cla_inc: &mut f64);
    fn count(&self, alive: bool) -> usize;
    fn check(&self);
}

/// For usize
pub trait ClauseIdIF {
    fn to_id(&self) -> ClauseId;
    fn to_index(&self) -> ClauseIndex;
    fn to_kind(&self) -> usize;
    fn is(&self, kind: ClauseKind, ix: ClauseIndex) -> bool;
    fn fmt(&self) -> String;
}

pub trait Delete<T> {
    fn delete<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
    fn delete_unstable<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
}

pub trait EmaIF {
    /// returns a new EMA from a flag (slow or fast) and a window size
    fn get(&self) -> f64;
    /// returns an EMA value
    fn update(&mut self, x: f64) -> ();
    /// reset (equalize) both values
    fn reset(&mut self) -> ();
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

/// For VecDeque<usize>
pub trait QueueOperations {
    fn average(&self) -> f64;
    fn enqueue(&mut self, lim: usize, x: usize) -> bool;
    fn is_full(&self, lim: usize) -> bool;
}

/// For Solver
pub trait Restart {
    fn block_restart(&mut self, lbd: usize, clv: usize, blv: usize, nas: usize) -> ();
    fn force_restart(&mut self) -> ();
}

pub trait SatSolver {
    fn solve(&mut self) -> SolverResult;
    fn build(path: &str) -> (Solver, CNFDescription);
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

pub trait SolverStateIF {
    fn new(nv: usize, se: i32, fname: &str) -> SolverState;
    // print a progress report
    fn progress(
        &mut self,
        asgs: &AssignStack,
        config: &mut SolverConfiguration,
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
    fn bump_activity(&mut self, d: f64);
}

pub trait VarIdIF {
    /// converter from [VarId](type.VarId.html) to [Lit](type.Lit.html).
    /// returns a positive literal if p == LTRUE or BOTTOM.
    fn lit(&self, p: Lbool) -> Lit;
}

/// For [Var]
pub trait VarManagement {
    fn assigned(&self, l: Lit) -> Lbool;
    fn locked(&self, ch: &ClauseHead, cid: ClauseId) -> bool;
    fn satisfies(&self, c: &[Lit]) -> bool;
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize;
    fn attach_clause(
        &mut self,
        cid: ClauseId,
        ch: &mut ClauseHead,
        ignorable: bool,
        elim: &mut Eliminator,
    ) -> ();
    fn detach_clause(&mut self, cid: ClauseId, ch: &ClauseHead, elim: &mut Eliminator) -> ();
}

pub trait VarOrderIF {
    /// renamed from incrementHeap, updateVO
    fn update(&mut self, vec: &[Var], v: VarId);
    /// renamed from undoVO
    fn insert(&mut self, vec: &[Var], vi: VarId);
    fn clear(&mut self);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    /// Heap operations; renamed from selectVO
    fn select_var(&mut self, vars: &[Var]) -> VarId;
    fn rebuild(&mut self, vars: &[Var]);
    fn new(n: usize, init: usize) -> VarIdHeap;
    fn check(&self, s: &str);
    /// renamed from getHeapDown
    fn remove(&mut self, vec: &[Var], vs: VarId);
}

/// For Vec<Watch>
pub trait WatchManagement {
    fn initialize(self, n: usize) -> Self;
    fn count(&self) -> usize;
    fn attach(&mut self, blocker: Lit, c: usize);
    fn detach(&mut self, n: usize);
    fn detach_with(&mut self, cix: usize);
}

use crate::clause::{Clause, ClauseDB};
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::propagator::AssignStack;
use crate::solver::{Solver, SolverResult};
use crate::state::State;
use crate::types::{CNFDescription, ClauseId, Flag, Lbool, Lit, MaybeInconsistent, VarId};
use crate::var::Var;

/// API for Clause, providing `kill`.
pub trait ClauseIF {
    fn kill(&mut self, touched: &mut [bool]);
}

/// API for clause management like `reduce`, `simplify`, `new_clause`, and so on.
pub trait ClauseDBIF {
    fn new(nv: usize, nc: usize) -> Self;
    fn attach(&mut self, state: &mut State, vars: &mut [Var], lbd: usize) -> ClauseId;
    fn detach(&mut self, cid: ClauseId);
    fn reduce(&mut self, state: &mut State, vars: &mut [Var]);
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        elim: &mut Eliminator,
        state: &mut State,
        vars: &mut [Var],
    ) -> MaybeInconsistent;
    fn garbage_collect(&mut self);
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool) -> ClauseId;
    fn reset_lbd(&mut self, vars: &[Var], temp: &mut [usize]);
    fn bump_activity(&mut self, inc: &mut f64, cid: ClauseId);
    fn count(&self, alive: bool) -> usize;
    fn countf(&self, mask: u16) -> usize;
}

/// API for Clause Id like `to_lit`, `is_lifted_lit` and so on.
pub trait ClauseIdIF {
    fn to_lit(self) -> Lit;
    fn is_lifted_lit(self) -> bool;
    fn format(self) -> String;
}

/// API for O(n) deletion from a list, providing `delete_unstable`.
pub trait Delete<T> {
    fn delete_unstable<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
}

/// API for Eliminator like `activate`, `stop`, `eliminate` and so on.
pub trait EliminatorIF {
    fn new(nv: usize) -> Eliminator;
    fn activate(&mut self);
    fn stop(&mut self, cdb: &mut ClauseDB, vars: &mut [Var]);
    fn is_running(&self) -> bool;
    fn prepare(&mut self, cdb: &mut ClauseDB, vars: &mut [Var], force: bool);
    fn enqueue_clause(&mut self, cid: ClauseId, c: &mut Clause);
    fn clear_clause_queue(&mut self, cdb: &mut ClauseDB);
    fn clause_queue_len(&self) -> usize;
    fn enqueue_var(&mut self, vars: &mut [Var], vi: VarId, upword: bool);
    fn clear_var_queue(&mut self, vars: &mut [Var]);
    fn var_queue_len(&self) -> usize;
    fn eliminate(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        state: &mut State,
        vars: &mut [Var],
    ) -> MaybeInconsistent;
    fn extend_model(&mut self, model: &mut Vec<i32>);
    fn add_cid_occur(&mut self, vars: &mut [Var], cid: ClauseId, c: &mut Clause, enqueue: bool);
    fn remove_lit_occur(&mut self, vars: &mut [Var], l: Lit, cid: ClauseId);
    fn remove_cid_occur(&mut self, vars: &mut [Var], cid: ClauseId, c: &mut Clause);
}

/// API for Exponential Moving Average, EMA, like `get`, `reset`, `update` and so on.
pub trait EmaIF {
    fn new(f: usize) -> Self;
    fn get(&self) -> f64;
    fn reset(&mut self) {}
    fn update(&mut self, x: f64);
}

/// API for [object properties](../types/enum.Flag.html) like `is`, `turn_off`, `turn_on` and so on.
pub trait FlagIF {
    fn is(&self, flag: Flag) -> bool;
    fn turn_off(&mut self, flag: Flag);
    fn turn_on(&mut self, flag: Flag);
}

/// API for Literal like `from_int`, `from_var`, `to_cid` and so on.
pub trait LitIF {
    fn from_int(x: i32) -> Self;
    fn from_var(vi: VarId, p: Lbool) -> Self;
    fn vi(self) -> VarId;
    fn int(self) -> i32;
    fn lbool(self) -> Lbool;
    fn positive(self) -> bool;
    fn negate(self) -> Lit;
    fn to_cid(self) -> ClauseId;
}

/// API for assignemnet like `propagate`, `enqueue`, `cancel_until`, and so on.
pub trait PropagatorIF {
    fn new(n: usize) -> Self;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn level(&self) -> usize;
    fn is_zero(&self) -> bool;
    fn num_at(&self, n: usize) -> usize;
    fn remains(&self) -> bool;
    fn assigned(&self, l: Lit) -> Lbool;
    fn propagate(&mut self, cdb: &mut ClauseDB, state: &mut State, vars: &mut [Var]) -> ClauseId;
    fn cancel_until(&mut self, vars: &mut [Var], lv: usize);
    fn enqueue(&mut self, v: &mut Var, sig: Lbool, cid: ClauseId, dl: usize) -> MaybeInconsistent;
    fn enqueue_null(&mut self, v: &mut Var, sig: Lbool);
    fn uncheck_enqueue(&mut self, vars: &mut [Var], l: Lit, cid: ClauseId);
    fn uncheck_assume(&mut self, vars: &mut [Var], l: Lit);
    fn update_order(&mut self, vec: &[Var], v: VarId);
    fn select_var(&mut self, vars: &[Var]) -> VarId;
    fn dump_cnf(&mut self, cdb: &ClauseDB, config: &Config, vars: &[Var], fname: &str);
}

/// API for restart like `block_restart`, `force_restart` and so on.
pub trait RestartIF {
    fn block_restart(&mut self, asgs: &AssignStack, ncnfl: usize) -> bool;
    fn force_restart(&mut self, ncnfl: &mut f64) -> bool;
    fn restart_update_lbd(&mut self, lbd: usize);
    fn restart_update_asg(&mut self, n: usize);
    fn restart_update_luby(&mut self);
}

/// API for SAT solver like `build`, `solve` and so on.
pub trait SatSolverIF {
    fn build(config: Config, path: &str) -> (Solver, CNFDescription);
    fn solve(&mut self) -> SolverResult;
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

/// API for state/statistics management, providing `progress`.
pub trait StateIF {
    fn new(config: &Config, cnf: CNFDescription) -> State;
    fn adapt(&mut self, cdb: &mut ClauseDB);
    fn progress_header(&self);
    fn progress(&mut self, cdb: &ClauseDB, vars: &[Var], mes: Option<&str>);
}

/// API for SAT validator like `inject_assignment`, `validate` and so on.
pub trait ValidatorIF {
    fn inject_assigmnent(&mut self, vec: &[i32]) -> MaybeInconsistent;
    fn validate(&self) -> Option<Vec<i32>>;
}

/// API for Var, providing `new` and `new_vars`.
pub trait VarIF {
    fn new(i: usize) -> Var;
    fn new_vars(n: usize) -> Vec<Var>;
}

/// API for var DB like `assigned`, `locked`, `compute_lbd` and so on.
pub trait VarDBIF {
    fn assigned(&self, l: Lit) -> Lbool;
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool;
    fn satisfies(&self, c: &[Lit]) -> bool;
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize;
    fn bump_activity(&mut self, inc: &mut f64, vi: VarId);
}

/// API for watcher DB like `attach`, `detach`, `detach_with` and so on.
pub trait WatchDBIF {
    fn initialize(self, n: usize) -> Self;
    fn count(&self) -> usize;
    fn register(&mut self, blocker: Lit, c: usize);
    fn detach(&mut self, n: usize);
    fn detach_with(&mut self, cid: usize);
}

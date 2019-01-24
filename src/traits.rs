use crate::assign::AssignStack;
use crate::clause::{Clause, ClauseDB};
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::solver::{Solver, SolverResult};
use crate::state::State;
use crate::types::{CNFDescription, ClauseId, Flag, Lbool, Lit, VarId};
use crate::var::Var;

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
    fn cancel_until(&mut self, vars: &mut [Var], lv: usize);
    fn enqueue(&mut self, v: &mut Var, sig: Lbool, cid: ClauseId, dl: usize) -> bool;
    fn enqueue_null(&mut self, v: &mut Var, sig: Lbool, dl: usize) -> bool;
    fn uncheck_enqueue(&mut self, vars: &mut [Var], l: Lit, cid: ClauseId);
    fn uncheck_assume(&mut self, vars: &mut [Var], l: Lit);
    fn dump_cnf(&mut self, cdb: &ClauseDB, config: &Config, vars: &[Var], fname: &str);
    fn rebuild_order(&mut self, vars: &[Var]);
    fn update_order(&mut self, vec: &[Var], v: VarId);
    fn select_var(&mut self, vars: &[Var]) -> VarId;
}

pub trait ClauseIF {
    fn kill(&mut self, touched: &mut [bool]);
}

pub trait ClauseDBIF {
    fn new(nv: usize, nc: usize) -> Self;
    fn attach(
        &mut self,
        config: &mut Config,
        elim: &mut Eliminator,
        vars: &mut [Var],
        v: &mut Vec<Lit>,
        lbd: usize,
    ) -> ClauseId;
    fn detach(&mut self, cid: ClauseId);
    fn reduce(
        &mut self,
        asgs: &mut AssignStack,
        config: &Config,
        elim: &mut Eliminator,
        state: &mut State,
        vars: &mut [Var],
    );
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut Config,
        elim: &mut Eliminator,
        state: &mut State,
        vars: &mut [Var],
    ) -> bool;
    fn garbage_collect(&mut self, asgs: &mut AssignStack, vars: &mut [Var], elim: &mut Eliminator);
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool) -> ClauseId;
    fn reset_lbd(&mut self, vars: &[Var], temp: &mut [usize]);
    fn bump_activity(&mut self, inc: &mut f64, cid: ClauseId);
    fn count(&self, alive: bool) -> usize;
}

pub trait ClauseIdIF {
    fn to_lit(self) -> Lit;
    fn is_lifted_lit(self) -> bool;
    fn format(self) -> String;
}

pub trait Delete<T> {
    fn delete_unstable<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
}

pub trait EliminatorIF {
    fn new(use_elim: bool) -> Eliminator;
    fn stop(&mut self, cdb: &mut ClauseDB, vars: &mut [Var], force: bool);
    fn enqueue_clause(&mut self, cid: ClauseId, c: &mut Clause);
    fn clear_clause_queue(&mut self, cdb: &mut ClauseDB);
    fn clause_queue_len(&self) -> usize;
    fn enqueue_var(&mut self, v: &mut Var);
    fn clear_var_queue(&mut self, vars: &mut [Var]);
    fn var_queue_len(&self) -> usize;
    fn eliminate(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        config: &mut Config,
        state: &mut State,
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

pub trait FlagIF {
    fn is(&self, flag: Flag) -> bool;
    fn turn_off(&mut self, flag: Flag);
    fn turn_on(&mut self, flag: Flag);
}

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

pub trait Propagate {
    fn propagate(&mut self, cdb: &mut ClauseDB, state: &mut State, vars: &mut [Var]) -> ClauseId;
}

pub trait RestartIF {
    fn block_restart(&mut self, asgs: &AssignStack, config: &Config, ncnfl: usize) -> bool;
    fn force_restart(&mut self, config: &mut Config, ncnfl: &mut f64) -> bool;
    fn restart_update_lbd(&mut self, lbd: usize);
    fn restart_update_asg(&mut self, config: &Config, n: usize);
    fn restart_update_luby(&mut self, config: &mut Config);
}

pub trait SatSolverIF {
    fn build(config: Config, path: &str) -> (Solver, CNFDescription);
    fn solve(&mut self) -> SolverResult;
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

pub trait StateIF {
    fn new(config: &Config, nv: usize, se: i32, fname: &str) -> State;
    fn progress_header(&self, config: &Config);
    fn progress(
        &mut self,
        cdb: &ClauseDB,
        config: &mut Config,
        elim: &Eliminator,
        vars: &[Var],
        mes: Option<&str>,
    );
}

pub trait ValidatorIF {
    fn inject_assigmnent(&mut self, vec: &[i32]);
    fn validate(&self) -> Option<Vec<i32>>;
}

pub trait VarIF {
    fn new(i: usize) -> Var;
    fn new_vars(n: usize) -> Vec<Var>;
}

pub trait VarDBIF {
    fn assigned(&self, l: Lit) -> Lbool;
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool;
    fn satisfies(&self, c: &[Lit]) -> bool;
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize;
    fn attach(&mut self, elim: &mut Eliminator, cid: ClauseId, c: &mut Clause, enqueue: bool);
    fn detach(&mut self, elim: &mut Eliminator, cid: ClauseId, c: &Clause);
    fn bump_activity(&mut self, inc: &mut f64, vi: VarId);
}

pub trait WatchDBIF {
    fn initialize(self, n: usize) -> Self;
    fn count(&self) -> usize;
    fn attach(&mut self, blocker: Lit, c: usize);
    fn detach(&mut self, n: usize);
    fn detach_with(&mut self, cid: usize);
}

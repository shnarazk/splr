use crate::clause::{Clause, ClauseDB};
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::propagator::AssignStack;
use crate::solver::{Solver, SolverResult};
use crate::state::State;
use crate::types::{CNFDescription, ClauseId, Flag, Lbool, Lit, MaybeInconsistent, VarId};
use crate::var::{Var, VarDB};

/// API for Clause, providing `kill`.
pub trait ClauseIF {
    /// make a clause *dead*; the clause still exists in clause database as a garbage.
    fn kill(&mut self, touched: &mut [bool]);
}

/// API for clause management like `reduce`, `simplify`, `new_clause`, and so on.
pub trait ClauseDBIF {
    /// return a new instance
    fn new(config: &Config, nv: usize, nc: usize) -> Self;
    /// return the length of `clause`
    fn len(&self) -> usize;
    /// make a new clause from `state.new_learnt` and register it to clause database.
    /// return true if it's empty
    fn is_empty(&self) -> bool;
    fn attach(&mut self, state: &mut State, vars: &mut VarDB, lbd: usize) -> ClauseId;
    /// unregister a clause `cid` from clause database and make the clause dead.
    fn detach(&mut self, cid: ClauseId);
    /// halve the number of 'learnt' or *removable* clauses.
    fn reduce(&mut self, state: &mut State, vars: &mut VarDB);
    /// simplify database by:
    /// * removing satisfiable clauses
    /// * calling exhaustive simplifier that tries **clause subsumption** and **variable elimination**.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn simplify(
        &mut self,
        asgs: &mut AssignStack,
        elim: &mut Eliminator,
        state: &mut State,
        vars: &mut VarDB,
    ) -> MaybeInconsistent;
    fn reset(&mut self);
    /// delete *dead* clauses from database, which are made by:
    /// * `reduce`
    /// * `simplify`
    /// * `kill`
    fn garbage_collect(&mut self);
    /// allocate a new clause and return its id.
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool) -> ClauseId;
    /// re-calculate the lbd values of all (learnt) clauses.
    fn reset_lbd(&mut self, vars: &VarDB, temp: &mut [usize]);
    /// update clause activity.
    fn bump_activity(&mut self, cid: ClauseId);
    /// increment activity step.
    fn scale_activity(&mut self);
    /// return the number of alive clauses in the database. Or return the database size if `active` is `false`.
    fn count(&self, alive: bool) -> usize;
    /// return the number of clauses which satisfy given flags and aren't DEAD.
    fn countf(&self, mask: Flag) -> usize;
    /// record a clause to unsat certification
    fn certificate_add(&mut self, vec: &[Lit]);
    /// record a deleted clause to unsat certification
    fn certificate_delete(&mut self, vec: &[Lit]);
    /// delete satisfied clauses at decision level zero.
    fn eliminate_satisfied_clauses(&mut self, elim: &mut Eliminator, vars: &mut VarDB, occur: bool);
    /// emit an error if the db size (the number of clauses) is over the limit.
    fn check_size(&self) -> MaybeInconsistent;
    /// change good learnt clauses to permanent one
    fn make_permanent(&mut self, reinit: bool);
}

/// API for Clause Id like `to_lit`, `is_lifted_lit` and so on.
pub trait ClauseIdIF {
    /// convert a (lifted) clause id made from a `Lit` to Lit.
    fn to_lit(self) -> Lit;
    /// return `true` if a given clause id is made from a `Lit`.
    fn is_lifted_lit(self) -> bool;
    /// make a string for printing.
    fn format(self) -> String;
}

/// API for O(n) deletion from a list, providing `delete_unstable`.
pub trait Delete<T> {
    /// *O(n)* item deletion protocol.
    fn delete_unstable<F>(&mut self, filter: F)
    where
        F: FnMut(&T) -> bool;
}

/// API for Eliminator like `activate`, `stop`, `eliminate` and so on.
pub trait EliminatorIF {
    fn new(config: &Config, nv: usize) -> Eliminator;
    /// set eliminater's mode to **ready**.
    fn activate(&mut self);
    /// set eliminater's mode to **dormant**.
    fn stop(&mut self, cdb: &mut ClauseDB, vars: &mut VarDB);
    fn is_running(&self) -> bool;
    fn is_waiting(&self) -> bool;
    /// rebuild occur lists.
    fn prepare(&mut self, cdb: &mut ClauseDB, vars: &mut VarDB, force: bool);
    fn enqueue_clause(&mut self, cid: ClauseId, c: &mut Clause);
    fn clear_clause_queue(&mut self, cdb: &mut ClauseDB);
    fn clause_queue_len(&self) -> usize;
    fn enqueue_var(&mut self, vars: &mut VarDB, vi: VarId, upword: bool);
    fn clear_var_queue(&mut self, vars: &mut VarDB);
    fn var_queue_len(&self) -> usize;
    /// run clause subsumption and variable elimination.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn eliminate(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        state: &mut State,
        vars: &mut VarDB,
    ) -> MaybeInconsistent;
    /// add assignments for eliminated vars to `model`.
    fn extend_model(&mut self, model: &mut Vec<i32>);
    /// register a clause id to all corresponding occur lists.
    fn add_cid_occur(&mut self, vars: &mut VarDB, cid: ClauseId, c: &mut Clause, enqueue: bool);
    /// remove a clause id from literal's occur list.
    fn remove_lit_occur(&mut self, vars: &mut VarDB, l: Lit, cid: ClauseId);
    /// remove a clause id from all corresponding occur lists.
    fn remove_cid_occur(&mut self, vars: &mut VarDB, cid: ClauseId, c: &mut Clause);
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
    /// convert from `i32`.
    fn from_int(x: i32) -> Self;
    /// convert [VarId](../type.VarId.html) to [Lit](../type.Lit.html).
    /// It returns a positive literal if `p` is `TRUE` or `BOTTOM`.
    fn from_var(vi: VarId, p: Lbool) -> Self;
    /// convert to var index.
    fn vi(self) -> VarId;
    /// convert to `i32`.
    fn to_i32(self) -> i32;
    /// convert to `Lbool`.
    fn lbool(self) -> Lbool;
    /// return the sign or *phase*; return `true` if it is a positive literal.
    fn is_positive(self) -> bool;
    /// flip the sign.
    fn negate(self) -> Lit;
    /// lift a literal to a *virtual* clause id.
    fn to_cid(self) -> ClauseId;
}

pub trait ProgressEvaluator {
    type Input;
    fn update(&mut self, val: Self::Input);
    fn get(&self) -> f64;
    fn trend(&self) -> f64;
    fn is_active(&self) -> bool;
    fn new(config: &Config) -> Self;
}

/// API for assignment like `propagate`, `enqueue`, `cancel_until`, and so on.
pub trait PropagatorIF {
    fn new(n: usize) -> Self;
    /// return the number of assignments.
    fn len(&self) -> usize;
    /// return `true` if there's no assignment.
    fn is_empty(&self) -> bool;
    /// return the current decision level.
    fn level(&self) -> usize;
    /// return `true` if the current decision level is zero.
    fn is_zero(&self) -> bool;
    /// return the number of assignments at a given decision level `u`.
    fn num_at(&self, n: usize) -> usize;
    /// return `true` if there are unpropagated assignments.
    fn remains(&self) -> bool;
    /// return the *value* of a given literal.
    fn assigned(&self, l: Lit) -> Lbool;
    /// execute *propagate*.
    fn propagate(&mut self, cdb: &mut ClauseDB, state: &mut State, vars: &mut VarDB) -> ClauseId;
    /// execute *backjump*.
    fn cancel_until(&mut self, vars: &mut VarDB, lv: usize);
    /// add an assignment caused by a clause; emit an exception if solver becomes inconsistent.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by the new assignment.
    fn enqueue(&mut self, v: &mut Var, sig: Lbool, cid: ClauseId, dl: usize) -> MaybeInconsistent;
    /// add an assignment with no reason clause without inconsistency check.
    fn enqueue_null(&mut self, v: &mut Var, sig: Lbool);
    /// unsafe enqueue; doesn't emit an exception.
    fn uncheck_enqueue(&mut self, vars: &mut VarDB, l: Lit, cid: ClauseId);
    /// unsafe assume; doesn't emit an exception.
    fn uncheck_assume(&mut self, vars: &mut VarDB, l: Lit);
    /// update the internal heap on var order.
    fn update_order(&mut self, vec: &VarDB, v: VarId);
    /// select a new decision variable.
    fn select_var(&mut self, vars: &VarDB) -> VarId;
    /// dump all active clauses and fixed assignments in solver to a CNF file `fname`.
    fn dump_cnf(&mut self, cdb: &ClauseDB, state: &State, vars: &VarDB, fname: &str);
}

/// API for restart like `block_restart`, `force_restart` and so on.
pub trait RestartIF {
    /// return a new instance
    fn new(config: &Config) -> Self;
    /// block restart if needed.
    fn block_restart(&mut self) -> bool;
    /// force restart if needed.
    fn force_restart(&mut self) -> bool;
    /// initialize data for Luby restart.
    fn initialize_luby(&mut self);
    /// update data for Luby restart.
    fn update_luby(&mut self);
}

/// API for SAT solver like `build`, `solve` and so on.
pub trait SatSolverIF {
    /// make a solver for debug. Probably you should use `build` instead of this.
    fn new(config: &Config, cnf: &CNFDescription) -> Solver;
    /// make a solver and load a CNF into it.
    ///
    /// # Errors
    ///
    /// IO error by failing to load a CNF file.
    fn build(config: &Config) -> std::io::Result<Solver>;
    /// search an assignment.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent by an internal error.
    fn solve(&mut self) -> SolverResult;
    /// add a vector of `Lit` as a clause to the solver.
    fn add_unchecked_clause(&mut self, v: &mut Vec<Lit>) -> Option<ClauseId>;
}

/// API for state/statistics management, providing `progress`.
pub trait StateIF {
    /// return an initialized state based on solver configuration and data about a CNF file.
    fn new(config: &Config, cnf: CNFDescription) -> State;
    /// return the number of unsolved vars
    fn num_unsolved_vars(&self) -> usize;
    /// return `true` if it is timed out.
    fn is_timeout(&self) -> bool;
    /// change heuristics based on stat data.
    fn adapt_strategy(&mut self, cdb: &mut ClauseDB, vdb: &mut VarDB);
    /// write a header of stat data to stdio.
    fn progress_header(&self);
    /// write stat data to stdio.
    fn progress(&mut self, cdb: &ClauseDB, vars: &VarDB, mes: Option<&str>);
    fn flush(&self, mes: &str);
}

/// API for SAT validator like `inject_assignment`, `validate` and so on.
pub trait ValidatorIF {
    /// load a assignment set into solver.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn inject_assigmnent(&mut self, vec: &[i32]) -> MaybeInconsistent;
    /// return `true` is the loaded assignment set is satisfiable (a model of a problem).
    fn validate(&self) -> Option<Vec<i32>>;
}

/// API for Var, providing `new` and `new_vars`.
pub trait VarIF {
    fn new(i: usize) -> Var;
    fn new_vars(n: usize) -> Vec<Var>;
}

/// API for var DB like `assigned`, `locked`, `compute_lbd` and so on.
pub trait VarDBIF {
    /// return a new instance
    fn new(n: usize) -> Self;
    /// return the length of `vars`
    fn len(&self) -> usize;
    /// return true if it's empty
    fn is_empty(&self) -> bool;
    /// return the 'value' of a given literal.
    fn assigned(&self, l: Lit) -> Lbool;
    /// return `true` is the clause is the reason of the assignment.
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool;
    /// return `true` if the set of literals is satisfiable under the current assignment.
    fn satisfies(&self, c: &[Lit]) -> bool;
    /// copy some stat data from `State`
    fn update_stat(&mut self, state: &State);
    /// return a LBD value for the set of literals.
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize;
    /// update the variable's activity.
    fn bump_activity(&mut self, vi: VarId);
    /// increment activity step.
    fn scale_activity(&mut self);
}

/// API for 'watcher list' like `attach`, `detach`, `detach_with` and so on.
pub trait WatchDBIF {
    fn initialize(self, n: usize) -> Self;
    /// make a new 'watch', and add it to this watcher list.
    fn register(&mut self, blocker: Lit, c: ClauseId);
    /// remove *n*-th clause from the watcher list. *O(1)* operation.
    fn detach(&mut self, n: usize);
    /// remove a clause which id is `cid` from the watcher list. *O(n)* operation.
    fn detach_with(&mut self, cid: ClauseId);
    /// update blocker of cid.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit);
}

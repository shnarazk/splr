/// Crate `assign` implements Boolean Constraint Propagation and decision var selection.
/// This version can handle Chronological and Non Chronological Backtrack.
mod heap;
/// EMA of activity
mod progress;
/// Boolean constraint propagation
mod propagate;
/// Var rewarding
#[cfg_attr(feature = "EVSIDS", path = "evsids.rs")]
#[cfg_attr(not(feature = "EVSIDS"), path = "learning_rate.rs")]
mod reward;
/// Decision var selection
mod select;
/// assignment management
mod stack;
/// var struct and its methods
mod var;

pub use self::{
    progress::{ProgressACT, ProgressCPR},
    propagate::PropagateIF,
    select::VarSelectIF,
    stack::ClauseManipulateIF,
    var::VarManipulateIF,
};

use {
    self::heap::{VarHeapIF, VarOrderIF},
    super::{cdb::ClauseDBIF, state::State, types::*},
    std::{ops::Range, slice::Iter},
};

/// API for var rewarding.
pub trait VarRewardIF {
    /// return var's activity.
    fn activity(&mut self, vi: VarId) -> f64;
    /// initialize rewards based on an order of vars.
    fn initialize_reward(&mut self, iterator: Iter<'_, usize>);
    /// clear var's activity
    fn clear_reward(&mut self, vi: VarId);
    /// modify var's activity at conflict analysis in `analyze`.
    fn reward_at_analysis(&mut self, vi: VarId);
    /// modify var's activity at value assignment in `uncheck_{assume, enqueue, fix}`.
    fn reward_at_assign(&mut self, vi: VarId);
    /// modify var's activity at value unassigment in `cancel_until`.
    fn reward_at_unassign(&mut self, vi: VarId);
    /// update internal counter.
    fn reward_update(&mut self);
    /// update reward setting as a part of module adoptation.
    fn adjust_reward(&mut self, state: &State);
}

/// API for assignment like `propagate`, `enqueue`, `cancel_until`, and so on.
pub trait AssignIF:
    ClauseManipulateIF
    + PropagateIF
    + VarManipulateIF
    + VarRewardIF
    + VarSelectIF
    + Export<(usize, usize, usize, f64), ()>
{
    /// return a literal in the stack.
    fn stack(&self, i: usize) -> Lit;
    /// return literals in the range of stack.
    fn stack_range(&self, r: Range<usize>) -> &[Lit];
    /// return the number of assignments.
    fn stack_len(&self) -> usize;
    /// return the number of assignments at a given decision level `u`.
    ///
    /// ## Caveat
    /// - it emits a panic by out of index range.
    /// - it emits a panic if the level is 0.
    fn len_upto(&self, n: DecisionLevel) -> usize;
    /// return `true` if there's no assignment.
    fn stack_is_empty(&self) -> bool;
    /// return an iterator over assignment stack.
    fn stack_iter(&self) -> Iter<'_, Lit>;
    /// return the current decision level.
    fn decision_level(&self) -> DecisionLevel;
    ///return the decision var's id at that level.
    fn decision_vi(&self, lv: DecisionLevel) -> VarId;
    /// return `true` if there are unpropagated assignments.
    fn remains(&self) -> bool;
    /// return `true` if subsequential propagations emit the same conflict.
    fn recurrent_conflicts(&self) -> bool;
    /// return a reference to `aasign`.
    fn assign_ref(&self) -> &[Option<bool>];
    /// return a reference to `level`.
    fn level_ref(&self) -> &[DecisionLevel];
    fn best_assigned(&mut self, flag: Flag) -> usize;
    /// inject assignments for eliminated vars.
    fn extend_model<C>(&mut self, c: &mut C, lits: &[Lit]) -> Vec<Option<bool>>
    where
        C: ClauseDBIF;
}

/// Reasons of assignments, two kinds
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssignReason {
    /// One of not assigned, assigned by decision, or asserted.
    None,
    /// Assigned by a clause. If it is binary, the reason literal is stored in the 2nd.
    Implication(ClauseId, Lit),
}

/// Object representing a variable.
#[derive(Debug)]
pub struct Var {
    /// reverse conversion to index. Note `VarId` must be `usize`.
    pub index: VarId,
    /// the number of participation in conflict analysis
    participated: u32,
    /// a dynamic evaluation criterion like EVSIDS or ACID.
    reward: f64,
    /// the number of conflicts at which this var was assigned lastly.
    timestamp: usize,
    /// the `Flag`s
    flags: Flag,
}

/// A record of assignment. It's called 'trail' in Glucose.
#[derive(Debug)]
pub struct AssignStack {
    /// assigns of vars
    assign: Vec<Option<bool>>,
    /// levels of vars
    level: Vec<DecisionLevel>,
    /// reason of assignment
    reason: Vec<AssignReason>,
    /// record of assignment
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    q_head: usize,
    pub root_level: DecisionLevel,
    conflicts: (VarId, VarId),
    var_order: VarIdHeap, // Variable Order
    temp_order: Vec<Lit>,

    //
    //## Phase handling
    //
    use_rephase: bool,
    best_assign: bool,
    build_best_at: usize,
    num_best_assign: f64,

    //
    //## Statistics
    //
    /// the number of vars.
    pub num_vars: usize,
    /// the number of asserted vars.
    pub num_asserted_vars: usize,
    /// the number of eliminated vars.
    pub num_eliminated_vars: usize,
    pub num_conflict: usize,
    num_propagation: usize,
    num_restart: usize,
    cpr: ProgressCPR,

    //
    //## Var DB
    //
    /// an index for counting elapsed time
    ordinal: usize,
    /// vars
    var: Vec<Var>,

    //
    //## Var Rewarding
    //
    /// var activity decay
    activity_decay: f64,
    /// maximum var activity decay
    activity_decay_max: f64,
    /// ONLY used in feature EVSIDS
    reward_step: f64,
    /// Ema of activities
    activity_ema: ProgressACT,

    //
    //## Vivification
    //
    /// save old num_conflict, num_propagation, num_restart
    vivify_sandbox: (usize, usize, usize),
}

/// Heap of VarId, based on var activity.
// # Note
// - both fields has a fixed length. Don't use push and pop.
// - `idxs[0]` contains the number of alive elements
//   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Debug)]
pub struct VarIdHeap {
    /// order : usize -> VarId, -- Which var is the n-th best?
    heap: Vec<VarId>,
    /// VarId : -> order : usize -- How good is the var?
    /// idxs[0] contais the number of alive elements
    idxs: Vec<usize>,
}

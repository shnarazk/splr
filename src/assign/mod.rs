/// Crate `assign` implements Boolean Constraint Propagation and decision var selection.
/// This version can handle Chronological and Non Chronological Backtrack.
mod heap;
pub mod propagate;
pub mod reward;
pub mod select;
pub mod stack;
pub mod var;

pub use self::{
    propagate::PropagationIF,
    reward::{VarRewardIF, REWARDS, VRD_MAX},
    select::VarSelectionIF,
    stack::ClauseManipulationIF,
    var::VarManipulationIF,
};

use {
    self::heap::{VarHeapIF, VarOrderIF},
    super::types::*,
    std::{ops::Range, slice::Iter},
};

/// API for assignment like `propagate`, `enqueue`, `cancel_until`, and so on.
pub trait AssignIF: ClauseManipulationIF + PropagationIF + VarManipulationIF + VarRewardIF {
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
    fn level_ref(&self) -> &[DecisionLevel];
    fn best_assigned(&mut self, flag: Flag) -> usize;
    /// inject assignments for eliminated vars.
    fn extend_model(&mut self, lits: &[Lit]);
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssignReason {
    /// One of not assigned, assigned by decision, or solved.
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
    /// a dynamic evaluation criterion like VSIDS or ACID.
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

    //
    //## Phase handling
    //
    best_assign: bool,
    build_best_at: usize,
    num_best_assign: usize,

    target_assign: bool,
    build_target_at: usize,
    num_target_assign: usize,

    //
    //## Statistics
    //
    /// the number of vars.
    pub num_vars: usize,
    /// the number of solved vars.
    pub num_solved_vars: usize,
    /// the number of eliminated vars.
    pub num_eliminated_vars: usize,
    num_conflict: usize,
    num_propagation: usize,
    num_restart: usize,

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
    /// estimated number of hot variable
    pub core_size: Ema,
    /// mode
    reward_mode: RewardStep,
    /// ONLY used in feature EVSIDS
    reward_step: f64,
}

#[derive(Clone, Copy, Eq, Debug, PartialEq)]
pub enum RewardStep {
    HeatUp = 0,
    Annealing,
    Final,
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
    idxs: Vec<usize>,
}

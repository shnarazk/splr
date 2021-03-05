/// Crate `assign` implements Boolean Constraint Propagation and decision var selection.
/// This version can handle Chronological and Non Chronological Backtrack.
mod heap;
/// Boolean constraint propagation
mod propagate;
/// Var rewarding
#[cfg_attr(feature = "EVSIDS", path = "evsids.rs")]
#[cfg_attr(feature = "LR_rewarding", path = "learning_rate.rs")]
mod reward;
/// Decision var selection
mod select;
/// assignment management
mod stack;
/// var struct and its methods
mod var;

pub use self::{
    propagate::PropagateIF, select::VarSelectIF, stack::ClauseManipulateIF, var::VarManipulateIF,
};
#[cfg(any(feature = "best_phases_tracking", feature = "var_staging"))]
use std::collections::HashMap;
use {
    self::heap::{VarHeapIF, VarOrderIF},
    super::{cdb::ClauseDBIF, types::*},
    std::{ops::Range, slice::Iter},
};

/// API about assignment like [`decision_level`](`crate::assign::AssignIF::decision_level`), [`stack`](`crate::assign::AssignIF::stack`), [`best_assigned`](`crate::assign::AssignIF::best_assigned`), and so on.
pub trait AssignIF: ActivityIF<VarId> + ClauseManipulateIF + PropagateIF + VarManipulateIF {
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
    /// return `true` if there are un-propagated assignments.
    fn remains(&self) -> bool;
    /// return a reference to `assign`.
    fn assign_ref(&self) -> &[Option<bool>];
    /// return a reference to `level`.
    fn level_ref(&self) -> &[DecisionLevel];
    fn best_assigned(&mut self) -> Option<usize>;
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
#[derive(Clone, Debug)]
pub struct Var {
    /// reverse conversion to index. Note `VarId` must be `usize`.
    pub index: VarId,
    /// the number of participation in conflict analysis
    participated: u32,
    /// a dynamic evaluation criterion like EVSIDS or ACID.
    reward: f64,
    /// the number of conflicts at which this var was assigned an rewarded lastly.
    timestamp: usize,
    /// the `Flag`s
    flags: Flag,
}

/// A record of assignment. It's called 'trail' in Glucose.
#[derive(Clone, Debug)]
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
    var_order: VarIdHeap, // Variable Order

    //
    //## Phase handling
    //
    best_assign: bool,
    build_best_at: usize,
    num_best_assign: usize,
    rephasing: bool,
    #[cfg(feature = "best_phases_tracking")]
    best_phases: HashMap<VarId, (bool, AssignReason)>,

    //
    //## Stage handling
    //
    use_stage: bool,
    #[cfg(feature = "var_staging")]
    /// Decay rate for staging reward
    staging_reward_decay: f64,
    #[cfg(feature = "var_staging")]
    /// Bonus reward for vars on stage
    staging_reward_value: f64,
    #[cfg(feature = "var_staging")]
    staged_vars: HashMap<VarId, bool>,
    #[cfg(feature = "var_staging")]
    stage_mode_select: usize,
    num_stages: usize,
    stage_activity: f64,
    reward_index: usize,

    //
    //## Statistics
    //
    /// the number of vars.
    pub num_vars: usize,
    /// the number of asserted vars.
    pub num_asserted_vars: usize,
    /// the number of eliminated vars.
    pub num_eliminated_vars: usize,
    num_decision: usize,
    num_propagation: usize,
    pub num_conflict: usize,
    num_restart: usize,
    dpc_ema: EmaSU,
    ppc_ema: EmaSU,
    cpr_ema: EmaSU,

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
    /// the default value of var activity decay in configuration
    activity_decay_default: f64,
    /// its diff
    activity_anti_decay: f64,
    /// EMA of activity
    activity_ema: Ema,
    /// ONLY used in feature EVSIDS
    activity_decay_step: f64,

    //
    //## Vivification
    //
    during_vivification: bool,
    /// save old num_conflict, num_propagation, num_restart
    vivify_sandbox: (usize, usize, usize),
}

/// Heap of VarId, based on var activity.
// # Note
// - both fields has a fixed length. Don't use push and pop.
// - `idxs[0]` contains the number of alive elements
//   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Clone, Debug)]
pub struct VarIdHeap {
    /// order : usize -> VarId, -- Which var is the n-th best?
    heap: Vec<VarId>,
    /// VarId : -> order : usize -- How good is the var?
    /// `idxs[0]` holds the number of alive elements
    idxs: Vec<usize>,
}

impl<'a> ExportBox<'a, (&'a Ema, &'a Ema, &'a Ema)> for AssignStack {
    // returns references to EMAs:
    // 1. dpc = decision / conflict
    // 1. ppc = propagation / conflict
    // 1. cpr = conflict / restart
    fn exports_box(&'a self) -> Box<(&'a Ema, &'a Ema, &'a Ema)> {
        Box::from((
            self.dpc_ema.get_ema(),
            self.ppc_ema.get_ema(),
            self.cpr_ema.get_ema(),
        ))
    }
}

/// Crate `assign` implements Boolean Constraint Propagation and decision var selection.
/// This version can handle Chronological and Non Chronological Backtrack.
mod heap;
/// Boolean constraint propagation
mod propagate;
/// Var rewarding
#[cfg_attr(feature = "EVSIDS", path = "evsids.rs")]
#[cfg_attr(feature = "LRB_rewarding", path = "learning_rate.rs")]
mod reward;
/// Decision var selection
mod select;
/// assignment management
mod stack;
/// var struct and its methods
mod var;

pub use self::{propagate::PropagateIF, property::*, select::VarSelectIF, var::VarManipulateIF};
#[cfg(any(feature = "best_phases_tracking", feature = "rephase"))]
use std::collections::HashMap;
use {
    self::heap::{VarHeapIF, VarIdHeap},
    super::{cdb::ClauseDBIF, types::*},
    std::{fmt, ops::Range, slice::Iter},
};

/// API about assignment like [`decision_level`](`crate::assign::AssignIF::decision_level`), [`stack`](`crate::assign::AssignIF::stack`), [`best_assigned`](`crate::assign::AssignIF::best_assigned`), and so on.
pub trait AssignIF:
    ActivityIF<VarId>
    + Instantiate
    + PropagateIF
    + VarManipulateIF
    + PropertyDereference<property::Tusize, usize>
    + PropertyReference<property::TEma, Ema>
{
    /// return root level.
    fn root_level(&self) -> DecisionLevel;
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
    /// return `true` if the set of literals is satisfiable under the current assignment.
    fn satisfies(&self, c: &[Lit]) -> bool;
    /// return `true` is the clause is the reason of the assignment.
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool;
    /// dump the status as a CNF
    fn dump_cnf<C>(&mut self, cdb: &C, fname: &str)
    where
        C: ClauseDBIF;
}

/// Reasons of assignments, two kinds
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AssignReason {
    /// asserted
    Asserted(usize),
    /// Assigned by decision
    Decision(DecisionLevel),
    /// Assigned by a clause. If it is binary, the reason literal is stored in the 2nd.
    Implication(ClauseId, Lit),
    /// One of not assigned, assigned by decision, or asserted.
    None,
}

impl fmt::Display for AssignReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AssignReason::Asserted(t) => write!(f, "Asserted at {}", t),
            AssignReason::Decision(lvl) => write!(f, "Decided at level {}", lvl),
            AssignReason::Implication(cid, NULL_LIT) => write!(f, "Implied by {}", cid),
            AssignReason::Implication(cid, _) => write!(f, "Implied by B{}", cid),
            AssignReason::None => write!(f, "Not assigned"),
        }
    }
}

/// Object representing a variable.
#[derive(Clone, Debug)]
pub struct Var {
    /// reverse mapping to index. Note `VarId` must be `usize`.
    pub index: u32,
    /// the `Flag`s
    flags: Flag,
    /// the number of participation in conflict analysis
    participated: u32,
    /// a dynamic evaluation criterion like EVSIDS or ACID.
    reward: f64,
    /// the number of conflicts at which this var was assigned an rewarded lastly.
    timestamp: usize,

    #[cfg(feature = "boundary_check")]
    pub propagated_at: usize,
    #[cfg(feature = "boundary_check")]
    pub state: VarState,
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
    /// the-number-of-assigned-and-propagated-vars + 1
    q_head: usize,
    root_level: DecisionLevel,
    var_order: VarIdHeap, // Variable Order

    //
    //## Phase handling
    //
    best_assign: bool,
    build_best_at: usize,
    num_best_assign: usize,
    num_rephase: usize,
    bp_divergence_ema: Ema,

    #[cfg(feature = "best_phases_tracking")]
    best_phases: HashMap<VarId, (bool, AssignReason)>,
    #[cfg(feature = "rephase")]
    phase_age: usize,

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
    /// Decisions Per Conflict
    dpc_ema: EmaSU,
    /// Propagations Per Conflict
    ppc_ema: EmaSU,
    /// Conflicts Per Restart
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
    /// ONLY used in feature EVSIDS
    activity_decay_step: f64,

    //
    //## Vivification
    //
    during_vivification: bool,
}

#[cfg(feature = "boundary_check")]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Assign {
    pub at: usize,
    pub pos: Option<usize>,
    pub lvl: DecisionLevel,
    pub lit: i32,
    pub val: Option<bool>,
    pub by: AssignReason,
    pub state: VarState,
}

#[cfg(feature = "boundary_check")]
// return the list of composing literals:
// 1. literal itself
// 1. the value
// 1. the position in trail
// 1. last time propagated
// 1. its level
// 1. its assign reason
pub trait DebugReportIF {
    fn report(&self, asg: &AssignStack) -> Vec<Assign>;
}

#[cfg(feature = "boundary_check")]
fn make_lit_report(asg: &AssignStack, lit: &Lit) -> Assign {
    let vi = lit.vi();
    Assign {
        lit: i32::from(lit),
        val: asg.assigned(*lit),
        pos: asg.trail.iter().position(|l| vi == l.vi()),
        lvl: asg.level(vi),
        by: asg.reason(vi),
        at: asg.var(vi).propagated_at,
        state: asg.var[vi].state,
    }
}

#[cfg(feature = "boundary_check")]
impl DebugReportIF for Lit {
    fn report(&self, asg: &AssignStack) -> Vec<Assign> {
        vec![make_lit_report(asg, self)]
    }
}

#[cfg(feature = "boundary_check")]
impl DebugReportIF for [Lit] {
    fn report(&self, asg: &AssignStack) -> Vec<Assign> {
        self.iter()
            .map(|l| make_lit_report(asg, l))
            .collect::<Vec<_>>()
    }
}

#[cfg(feature = "boundary_check")]
impl DebugReportIF for Clause {
    fn report(&self, asg: &AssignStack) -> Vec<Assign> {
        let mut l = self
            .iter()
            .map(|l| make_lit_report(asg, l))
            .collect::<Vec<_>>();
        l.sort();
        l
    }
}

pub mod property {
    use super::AssignStack;
    use crate::types::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Tusize {
        NumConflict,
        NumDecision,
        NumPropagation,
        NumRephase,
        NumRestart,
        //
        //## var stat
        //
        NumVar,
        NumAssertedVar,
        NumEliminatedVar,
        /// the number of vars in `the unreachable core'
        NumUnassertedVar,
        NumUnassignedVar,
        NumUnreachableVar,
        RootLevel,
    }

    pub const USIZES: [Tusize; 12] = [
        Tusize::NumConflict,
        Tusize::NumDecision,
        Tusize::NumPropagation,
        Tusize::NumRephase,
        Tusize::NumRestart,
        Tusize::NumVar,
        Tusize::NumAssertedVar,
        Tusize::NumEliminatedVar,
        Tusize::NumUnassertedVar,
        Tusize::NumUnassignedVar,
        Tusize::NumUnreachableVar,
        Tusize::RootLevel,
    ];

    impl PropertyDereference<Tusize, usize> for AssignStack {
        #[inline]
        fn derefer(&self, k: Tusize) -> usize {
            match k {
                Tusize::NumConflict => self.num_conflict,
                Tusize::NumDecision => self.num_decision,
                Tusize::NumPropagation => self.num_propagation,
                Tusize::NumRephase => self.num_rephase,
                Tusize::NumRestart => self.num_restart,
                Tusize::NumVar => self.num_vars,
                Tusize::NumAssertedVar => self.num_asserted_vars,
                Tusize::NumEliminatedVar => self.num_eliminated_vars,
                Tusize::NumUnassertedVar => {
                    self.num_vars - self.num_asserted_vars - self.num_eliminated_vars
                }
                Tusize::NumUnassignedVar => {
                    self.num_vars
                        - self.num_asserted_vars
                        - self.num_eliminated_vars
                        - self.trail.len()
                }
                Tusize::NumUnreachableVar => self.num_vars - self.num_best_assign,
                Tusize::RootLevel => self.root_level as usize,
            }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum TEma {
        DecisionPerConflict,
        PropagationPerConflict,
        ConflictPerRestart,
        ConflictPerBaseRestart,
        BestPhaseDivergenceRate,
    }

    pub const EMAS: [TEma; 5] = [
        TEma::DecisionPerConflict,
        TEma::PropagationPerConflict,
        TEma::ConflictPerRestart,
        TEma::ConflictPerBaseRestart,
        TEma::BestPhaseDivergenceRate,
    ];

    impl PropertyReference<TEma, Ema> for AssignStack {
        #[inline]
        fn refer(&self, k: TEma) -> &Ema {
            match k {
                TEma::DecisionPerConflict => self.dpc_ema.get_ema(),
                TEma::PropagationPerConflict => self.ppc_ema.get_ema(),
                TEma::ConflictPerRestart => self.cpr_ema.get_ema(),
                TEma::ConflictPerBaseRestart => self.cpr_ema.get_ema(),
                TEma::BestPhaseDivergenceRate => &self.bp_divergence_ema,
            }
        }
    }
}

// Module `assign` implements Boolean Constraint Propagation and decision var selection.
// This version can handle Chronological and Non Chronological Backtrack.

/// Ema
mod ema;
/// Heap
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
/// trail saving
mod trail_saving;
/// var struct and its methods
mod var;

pub use self::{
    propagate::PropagateIF,
    property::*,
    select::VarSelectIF,
    stack::AssignStack,
    var::{Var, VarManipulateIF},
};
use {
    crate::{cdb::ClauseDBIF, types::*},
    std::{fmt, ops::Range, slice::Iter},
};

#[cfg(feature = "trail_saving")]
pub use self::trail_saving::TrailSavingIF;

/// API about assignment like
/// [`decision_level`](`crate::assign::AssignIF::decision_level`),
/// [`stack`](`crate::assign::AssignIF::stack`),
/// [`best_assigned`](`crate::assign::AssignIF::best_assigned`), and so on.
pub trait AssignIF:
    ActivityIF<VarId>
    + Instantiate
    + PropagateIF
    + VarManipulateIF
    + PropertyDereference<property::Tusize, usize>
    + PropertyReference<property::TEma, EmaView>
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
    fn assign_ref(&self) -> Vec<Option<bool>>;
    /// return the largest number of assigned vars.
    fn best_assigned(&mut self) -> Option<usize>;
    /// return `true` if no best_phases
    #[cfg(feature = "rephase")]
    fn best_phases_invalid(&self) -> bool;
    /// inject assignments for eliminated vars.
    fn extend_model(&mut self, c: &mut impl ClauseDBIF) -> Vec<Option<bool>>;
    /// return `true` if the set of literals is satisfiable under the current assignment.
    fn satisfies(&self, c: &[Lit]) -> bool;
}

/// Reasons of assignments
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AssignReason {
    /// Implication by binary clause
    BinaryLink(Lit),
    /// Assigned by decision
    Decision(DecisionLevel),
    /// Assigned by a non-binary clause.
    Implication(ClauseId),
    /// None of the above.
    None,
}

impl fmt::Display for AssignReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &AssignReason::BinaryLink(_) => write!(f, "Implied by a binary clause"),
            AssignReason::Decision(0) => write!(f, "Asserted"),
            AssignReason::Decision(lvl) => write!(f, "Decided at level {lvl}"),
            AssignReason::Implication(cid) => write!(f, "Implied by {cid}"),
            AssignReason::None => write!(f, "Not assigned"),
        }
    }
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
    use super::stack::AssignStack;
    use crate::types::*;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
        NumReconflict,
        NumRepropagation,
        /// the number of vars in `the unreachable core'
        NumUnassertedVar,
        NumUnassignedVar,
        NumUnreachableVar,
        RootLevel,
    }

    pub const USIZES: [Tusize; 14] = [
        Tusize::NumConflict,
        Tusize::NumDecision,
        Tusize::NumPropagation,
        Tusize::NumRephase,
        Tusize::NumRestart,
        Tusize::NumVar,
        Tusize::NumAssertedVar,
        Tusize::NumEliminatedVar,
        Tusize::NumReconflict,
        Tusize::NumRepropagation,
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
                Tusize::NumReconflict => self.num_reconflict,
                Tusize::NumRepropagation => self.num_repropagation,
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

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Tf64 {
        AverageVarActivity,
        CurrentWorkingSetSize,
        VarDecayRate,
    }

    pub const F64S: [Tf64; 3] = [
        Tf64::AverageVarActivity,
        Tf64::CurrentWorkingSetSize,
        Tf64::VarDecayRate,
    ];

    impl PropertyDereference<Tf64, f64> for AssignStack {
        #[inline]
        fn derefer(&self, k: Tf64) -> f64 {
            match k {
                Tf64::AverageVarActivity => 0.0,    // self.activity_averaged,
                Tf64::CurrentWorkingSetSize => 0.0, // self.cwss,
                Tf64::VarDecayRate => self.activity_decay,
            }
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum TEma {
        AssignRate,
        DecisionPerConflict,
        PropagationPerConflict,
        ConflictPerRestart,
        ConflictPerBaseRestart,
        BestPhaseDivergenceRate,
    }

    pub const EMAS: [TEma; 6] = [
        TEma::AssignRate,
        TEma::DecisionPerConflict,
        TEma::PropagationPerConflict,
        TEma::ConflictPerRestart,
        TEma::ConflictPerBaseRestart,
        TEma::BestPhaseDivergenceRate,
    ];

    impl PropertyReference<TEma, EmaView> for AssignStack {
        #[inline]
        fn refer(&self, k: TEma) -> &EmaView {
            match k {
                TEma::AssignRate => self.assign_rate.as_view(),
                TEma::DecisionPerConflict => self.dpc_ema.as_view(),
                TEma::PropagationPerConflict => self.ppc_ema.as_view(),
                TEma::ConflictPerRestart => self.cpr_ema.as_view(),
                TEma::ConflictPerBaseRestart => self.cpr_ema.as_view(),
                TEma::BestPhaseDivergenceRate => self.bp_divergence_ema.as_view(),
            }
        }
    }
}

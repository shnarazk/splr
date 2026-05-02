// Module `assign` implements Boolean Constraint Propagation and decision var selection.
// This version can handle Chronological and Non Chronological Backtrack.

/// Heap
mod heap;
/// Var rewarding
mod learning_rate;
/// Boolean constraint propagation
mod propagate;
/// Decision var selection
mod select;
/// assignment management
mod stack;
/// trail saving
mod trail_saving;

pub use self::{
    learning_rate::VarActivityScheme,
    propagate::PropagateIF,
    property::*,
    select::{PhaseRotation, VarSelectIF},
    stack::{AssignStack, VarManipulateIF},
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
    ///
    /// CAVEAT: this return a wrong value under chrono_BT
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
    /// inject assignments for eliminated vars.
    fn extend_model(&mut self, c: &mut impl ClauseDBIF) -> Vec<Option<bool>>;
    /// return `true` if the set of literals is satisfiable under the current assignment.
    fn satisfies(&self, c: &[Lit]) -> bool;
    /// compute Literal Block Distance (LBD) of a slice of literals under the current assignment.
    fn literal_block_distance(&mut self, lits: &[Lit]) -> DecisionLevel;
    /// compute Literal Block Distance (LBD) of a slice of literals under the current immutable assignment.
    fn literal_block_distance_(&self, lits: &[Lit]) -> usize;
    /// return current var activity scheme
    fn activity_scheme(&self) -> &VarActivityScheme;
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

pub mod property {
    use super::stack::AssignStack;
    use crate::types::*;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Tusize {
        NumConflict,
        NumDecision,
        NumPropagation,
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

    pub const USIZES: [Tusize; 13] = [
        Tusize::NumConflict,
        Tusize::NumDecision,
        Tusize::NumPropagation,
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
        VarLearningRate,
    }

    pub const F64S: [Tf64; 3] = [
        Tf64::AverageVarActivity,
        Tf64::CurrentWorkingSetSize,
        Tf64::VarLearningRate,
    ];

    impl PropertyDereference<Tf64, f64> for AssignStack {
        #[inline]
        fn derefer(&self, k: Tf64) -> f64 {
            match k {
                Tf64::AverageVarActivity => 0.0,    // self.activity_averaged,
                Tf64::CurrentWorkingSetSize => 0.0, // self.cwss,
                Tf64::VarLearningRate => 1.0 - self.activity_stay_rate,
            }
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum TEma {
        DecisionPerConflict,
        PropagationPerConflict,
        ConflictPerRestart,
        ConflictPerBaseRestart,
        ConlictDistanceAverage,
    }

    pub const EMAS: [TEma; 5] = [
        TEma::DecisionPerConflict,
        TEma::PropagationPerConflict,
        TEma::ConflictPerRestart,
        TEma::ConflictPerBaseRestart,
        TEma::ConlictDistanceAverage,
    ];

    impl PropertyReference<TEma, EmaView> for AssignStack {
        #[inline]
        fn refer(&self, k: TEma) -> &EmaView {
            match k {
                TEma::DecisionPerConflict => self.dpc_ema.as_view(),
                TEma::PropagationPerConflict => self.ppc_ema.as_view(),
                TEma::ConflictPerRestart => self.cpr_ema.as_view(),
                TEma::ConflictPerBaseRestart => self.cpr_ema.as_view(),
                TEma::ConlictDistanceAverage => self.conflict_interval_average.0.as_view(),
            }
        }
    }
}

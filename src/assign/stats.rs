use super::stack::AssignStack;
use crate::{types::*, var_vector::VarRef};

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
    Tusize::NumRephase,
    Tusize::NumRestart,
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
            Tusize::NumConflict => self.num_conflicts,
            Tusize::NumDecision => self.num_decisions,
            Tusize::NumPropagation => self.num_propagations,
            Tusize::NumRephase => self.num_rephase,
            Tusize::NumRestart => self.num_restarts,
            Tusize::NumAssertedVar => self.num_asserted_vars,
            Tusize::NumEliminatedVar => self.num_eliminated_vars,
            Tusize::NumReconflict => self.num_reconflict,
            Tusize::NumRepropagation => self.num_repropagation,
            Tusize::NumUnassertedVar => {
                VarRef::num_vars() - self.num_asserted_vars - self.num_eliminated_vars
            }
            Tusize::NumUnassignedVar => {
                VarRef::num_vars()
                    - self.num_asserted_vars
                    - self.num_eliminated_vars
                    - self.trail.len()
            }
            Tusize::NumUnreachableVar => VarRef::num_vars() - self.num_best_assign,
            Tusize::RootLevel => self.root_level as usize,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Tf64 {
    AverageVarActivity,
    CurrentWorkingSetSize,
}

pub const F64S: [Tf64; 2] = [Tf64::AverageVarActivity, Tf64::CurrentWorkingSetSize];

impl PropertyDereference<Tf64, f64> for AssignStack {
    #[inline]
    fn derefer(&self, k: Tf64) -> f64 {
        match k {
            Tf64::AverageVarActivity => 0.0,    // self.activity_averaged,
            Tf64::CurrentWorkingSetSize => 0.0, // self.cwss,
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

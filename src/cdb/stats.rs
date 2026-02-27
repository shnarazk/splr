use super::ClauseDB;
use crate::types::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Tusize {
    NumBiClause,
    NumBiClauseCompletion,
    NumBiLearnt,
    NumClause,
    NumLBD2,
    NumLearnt,
    NumReduction,
    NumReRegistration,
}

pub const USIZES: [Tusize; 8] = [
    Tusize::NumBiClause,
    Tusize::NumBiClauseCompletion,
    Tusize::NumBiLearnt,
    Tusize::NumClause,
    Tusize::NumLBD2,
    Tusize::NumLearnt,
    Tusize::NumReduction,
    Tusize::NumReRegistration,
];

impl PropertyDereference<Tusize, usize> for ClauseDB {
    #[inline]
    fn derefer(&self, k: Tusize) -> usize {
        match k {
            Tusize::NumClause => self.num_clauses,
            Tusize::NumBiClause => self.num_bi_clauses,
            Tusize::NumBiClauseCompletion => self.num_bi_clause_completion,
            Tusize::NumBiLearnt => self.num_bi_learnts,
            Tusize::NumLBD2 => self.num_lbd2,
            Tusize::NumLearnt => self.num_learnts,
            Tusize::NumReduction => self.num_reduction,
            Tusize::NumReRegistration => self.num_reregistration,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Tf64 {
    ReductionThreshold,
}

pub const F64: [Tf64; 1] = [Tf64::ReductionThreshold];

impl PropertyDereference<Tf64, f64> for ClauseDB {
    #[inline]
    fn derefer(&self, k: Tf64) -> f64 {
        match k {
            Tf64::ReductionThreshold => self.reduction_threshold,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TEma {
    Entanglement,
    LBD,
}

pub const EMAS: [TEma; 2] = [TEma::Entanglement, TEma::LBD];

impl PropertyReference<TEma, EmaView> for ClauseDB {
    #[inline]
    fn refer(&self, k: TEma) -> &EmaView {
        match k {
            TEma::Entanglement => self.lb_entanglement.as_view(),
            TEma::LBD => self.lbd.as_view(),
        }
    }
}

// Module `assign` implements Boolean Constraint Propagation and decision var selection.
// This version can handle Chronological and Non Chronological Backtrack.

/// Ema
mod ema;
/// Boolean constraint propagation
mod propagate;

#[cfg(feature = "rephase")]
/// rephasing
pub mod rephase;

/// assignment management
mod stack;
/// properties
pub mod stats;
/// trail saving
mod trail_saving;

pub use self::{propagate::PropagateIF, stack::AssignStack};
use {crate::types::*, std::fmt};

#[cfg(feature = "trail_saving")]
pub use self::trail_saving::TrailSavingIF;

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

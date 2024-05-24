/// Var struct and Database management API
use {
    crate::types::*,
    std::{
        fmt,
        slice::{Iter, IterMut},
    },
};

/// Object representing a variable.
#[derive(Clone, Debug)]
pub struct Var {
    /// assigns of vars
    pub(super) assign: Option<bool>,
    /// levels of vars
    pub(super) level: DecisionLevel,
    /// reason of assignment
    pub(crate) reason: AssignReason,

    /// the `Flag`s (8 bits)
    pub(super) flags: FlagVar,
    /// a dynamic evaluation criterion like EVSIDS or ACID.
    pub(super) activity: f64,
    // reward_ema: Ema2,
    #[cfg(feature = "boundary_check")]
    pub propagated_at: usize,
    #[cfg(feature = "boundary_check")]
    pub timestamp: usize,
    #[cfg(feature = "boundary_check")]
    pub state: VarState,
}

impl Default for Var {
    fn default() -> Var {
        Var {
            assign: None,
            level: DecisionLevel::default(),
            reason: AssignReason::None,
            flags: FlagVar::empty(),
            activity: 0.0,
            // reward_ema: Ema2::new(200).with_slow(4_000),
            #[cfg(feature = "boundary_check")]
            propagated_at: 0,
            #[cfg(feature = "boundary_check")]
            timestamp: 0,
            #[cfg(feature = "boundary_check")]
            state: VarState::Unassigned(0),
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(f, "V{{{}}}", st(FlagVar::ELIMINATED, ", eliminated"),)
    }
}

impl Var {
    /// return a new vector of $n$ `Var`s.
    pub fn new_vars(n: usize) -> Vec<Var> {
        vec![Var::default(); n + 1]
    }
    pub fn activity(&self) -> f64 {
        self.activity
    }
}

impl FlagIF for Var {
    type FlagType = FlagVar;
    #[inline]
    fn is(&self, flag: Self::FlagType) -> bool {
        self.flags.contains(flag)
    }
    #[inline]
    fn set(&mut self, f: Self::FlagType, b: bool) {
        self.flags.set(f, b);
    }
    #[inline]
    fn turn_off(&mut self, flag: Self::FlagType) {
        self.flags.remove(flag);
    }
    #[inline]
    fn turn_on(&mut self, flag: Self::FlagType) {
        self.flags.insert(flag);
    }
    #[inline]
    fn toggle(&mut self, flag: Self::FlagType) {
        self.flags.toggle(flag);
    }
}

/// Var manipulation
pub trait VarManipulateIF {
    /// return the assignment of var.
    fn assign(&self, vi: VarId) -> Option<bool>;
    /// return *the value* of a literal.
    fn assigned(&self, l: Lit) -> Option<bool>;
    /// return the assign level of var.
    fn level(&self, vi: VarId) -> DecisionLevel;
    /// return the reason of assignment.
    fn reason(&self, vi: VarId) -> AssignReason;
    /// return the var.
    fn var(&self, vi: VarId) -> &Var;
    /// return the var.
    fn var_mut(&mut self, vi: VarId) -> &mut Var;
    /// return an iterator over Vars.
    fn var_iter(&self) -> Iter<'_, Var>;
    /// return an mutable iterator over Vars.
    fn var_iter_mut(&mut self) -> IterMut<'_, Var>;
    /// set var status to asserted.
    fn make_var_asserted(&mut self, vi: VarId);
    /// set var status to eliminated.
    fn make_var_eliminated(&mut self, vi: VarId);
}

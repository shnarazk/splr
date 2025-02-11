//! Var struct and Database management API
use {
    // super::{heap::VarHeapIF, stack::AssignStack, AssignIF},
    crate::types::{flags::FlagIF, flags::FlagVar, AssignReason, DecisionLevel},
    std::fmt,
};

/// Object representing a variable.
#[derive(Clone, Debug)]
pub struct Var {
    /// assignment
    pub(crate) assign: Option<bool>,
    /// decision level
    pub(crate) level: DecisionLevel,
    /// assign Reason
    pub(crate) reason: AssignReason,
    /// last reason for assignment.
    #[cfg(feature = "trail_saving")]
    pub(crate) reason_saved: AssignReason,
    /// the `Flag`s (8 bits)
    pub(crate) flags: FlagVar,
    /// a dynamic evaluation criterion like EVSIDS or ACID.
    pub(crate) activity: f64,
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
            level: 0,
            reason: AssignReason::None,
            #[cfg(feature = "trail_saving")]
            reason_saved: AssignReason::None,
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

impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        self == other
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
        (0..n as u32 + 1)
            .map(|n| {
                Var {
                    level: n, // each literal occupies a single level.
                    ..Default::default()
                }
            })
            .collect::<Vec<_>>()
    }
    pub fn activity(&self) -> f64 {
        self.activity
    }
    pub fn update_activity(&mut self, decay: f64, reward: f64) -> f64 {
        // Note: why the condition can be broken.
        //
        // 1. asg.ordinal += 1;
        // 1. handle_conflict -> cancel_until -> reward_at_unassign
        // 1. assign_by_implication -> v.timestamp = asg.ordinal
        // 1. restart
        // 1. cancel_until -> reward_at_unassign -> assertion failed
        //
        self.activity *= decay;
        if self.is(FlagVar::USED) {
            self.activity += reward;
            self.turn_off(FlagVar::USED);
        }
        // self.reward_ema.update(self.reward);
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

#[cfg(feature = "boundary_check")]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum VarState {
    AssertedSandbox(usize),
    Assigned(usize),
    AssignedSandbox(usize),
    Propagated(usize),
    Unassigned(usize),
}

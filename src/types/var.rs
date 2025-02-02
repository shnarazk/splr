/// Var struct and Database management API
use {
    crate::types::*,
    std::{fmt, hash::Hash},
};

/// 'Variable' identifier or 'variable' index, starting with one.
/// Implementation note: NonZeroUsize can be used but requires a lot of changes.
/// The current abstraction is incomplete.
pub type VarId = usize;

/// Object representing a variable.
#[derive(Clone, Debug)]
pub struct Var<'a> {
    /// variable id
    pub id: VarId,
    /// assignment
    pub assign: Option<bool>,
    /// decision level
    pub level: DecisionLevel,
    /// assign Reason
    pub reason: AssignReason<'a>,
    /// last reason for assignment.
    #[cfg(feature = "trail_saving")]
    pub reason_saved: AssignReason<'a>,
    /// the `Flag`s (8 bits)
    pub flags: FlagVar,
    /// a dynamic evaluation criterion like EVSIDS or ACID.
    pub activity: f64,
    // reward_ema: Ema2,
    #[cfg(feature = "boundary_check")]
    pub propagated_at: usize,
    #[cfg(feature = "boundary_check")]
    pub timestamp: usize,
    #[cfg(feature = "boundary_check")]
    pub state: VarState,
}

impl PartialEq for Var<'_> {
    fn eq(&self, other: &Var) -> bool {
        self.id == other.id
    }
}

impl Eq for Var<'_> {}

impl PartialOrd for Var<'_> {
    fn partial_cmp(&self, other: &Var) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

impl Ord for Var<'_> {
    fn cmp(&self, other: &Var) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl Hash for Var<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Default for Var<'_> {
    fn default() -> Var<'static> {
        Var {
            id: 0,
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

impl fmt::Display for Var<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(f, "V{{{}}}", st(FlagVar::ELIMINATED, ", eliminated"),)
    }
}

impl Var<'_> {
    /// return a new vector of $n$ `Var`s.
    pub fn new_vars(n: usize) -> Vec<Var<'static>> {
        (0..n as u32 + 1)
            .map(|n| {
                Var {
                    level: n, // each literal occupies a single level.
                    ..Default::default()
                }
            })
            .collect::<Vec<_>>()
    }
}

impl FlagIF for Var<'_> {
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

impl Var<'_> {
    pub(crate) fn make_asserted(&mut self) {
        self.reason = AssignReason::Decision(0);
        self.activity = 0.0;
        #[cfg(feature = "boundary_check")]
        {
            self.var[vi].timestamp = self.tick;
        }
    }
    pub(crate) fn make_eliminated(&mut self) {
        if !self.is(FlagVar::ELIMINATED) {
            self.turn_on(FlagVar::ELIMINATED);
            self.activity = 0.0;
            #[cfg(feature = "boundary_check")]
            {
                self.var[vi].timestamp = self.tick;
            }
        } else {
            #[cfg(feature = "boundary_check")]
            panic!("double elimination");
        }
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

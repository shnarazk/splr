/// Var struct and Database management API
use {
    super::{heap::VarHeapIF, stack::AssignStack, AssignIF},
    crate::types::*,
    std::{
        fmt,
        slice::{Iter, IterMut},
    },
};

/// Object representing a variable.
#[derive(Clone, Debug)]
pub struct Var {
    /// assignment
    pub(crate) assign: Option<bool>,
    /// decision level
    pub(super) level: DecisionLevel,
    /// assign Reason
    pub(super) reason: AssignReason,
    /// last reason for assignment.
    #[cfg(feature = "trail_saving")]
    pub(super) reason_saved: AssignReason,
    /// the `Flag`s (8 bits)
    pub(crate) flags: FlagVar,
    /// a dynamic evaluation criterion like EVSIDS or ACID.
    pub(super) reward: f64,
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
            reward: 0.0,
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
        self.reward
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

impl VarManipulateIF for AssignStack {
    fn assigned(&self, l: Lit) -> Option<bool> {
        match self.var[l.vi()].assign {
            Some(x) if !bool::from(l) => Some(!x),
            x => x,
        }
    }
    #[inline]
    fn assign(&self, vi: VarId) -> Option<bool> {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(vi).assign
        }
        #[cfg(not(feature = "unsafe_access"))]
        self.assign[vi]
    }
    #[inline]
    fn level(&self, vi: VarId) -> DecisionLevel {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(vi).level
        }
        #[cfg(not(feature = "unsafe_access"))]
        self.level[vi]
    }
    #[inline]
    fn reason(&self, vi: VarId) -> AssignReason {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(vi).reason
        }
        #[cfg(not(feature = "unsafe_access"))]
        self.reason[vi]
    }
    #[inline]
    fn var(&self, vi: VarId) -> &Var {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(vi)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.var[vi]
    }
    #[inline]
    fn var_mut(&mut self, vi: VarId) -> &mut Var {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked_mut(vi)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.var[vi]
    }
    fn var_iter(&self) -> Iter<'_, Var> {
        self.var.iter()
    }
    fn var_iter_mut(&mut self) -> IterMut<'_, Var> {
        self.var.iter_mut()
    }
    fn make_var_asserted(&mut self, vi: VarId) {
        self.var[vi].reason = AssignReason::Decision(0);
        self.set_activity(vi, 0.0);
        self.remove_from_heap(vi);

        #[cfg(feature = "boundary_check")]
        {
            self.var[vi].timestamp = self.tick;
        }

        #[cfg(feature = "best_phases_tracking")]
        self.check_best_phase(vi);
    }
    fn make_var_eliminated(&mut self, vi: VarId) {
        if !self.var[vi].is(FlagVar::ELIMINATED) {
            self.var[vi].turn_on(FlagVar::ELIMINATED);
            self.set_activity(vi, 0.0);
            self.remove_from_heap(vi);
            debug_assert_eq!(self.decision_level(), self.root_level);
            self.trail.retain(|l| l.vi() != vi);
            self.num_eliminated_vars += 1;

            #[cfg(feature = "boundary_check")]
            {
                self.var[vi].timestamp = self.tick;
            }

            #[cfg(feature = "trace_elimination")]
            {
                let lv = self.level[vi];
                if self.root_level == self.level[vi] && self.assign[vi].is_some() {
                    panic!("v:{}, dl:{}", self.var[vi], self.decision_level());
                }
                if !(self.root_level < self.level[vi] || self.assign[vi].is_none()) {
                    panic!(
                        "v:{}, lvl:{} => {}, dl:{}, assign:{:?} ",
                        self.var[vi],
                        lv,
                        self.level[vi],
                        self.decision_level(),
                        self.assign[vi],
                    );
                }
                debug_assert!(self.root_level < self.level[vi] || self.assign[vi].is_none());
            }
        } else {
            #[cfg(feature = "boundary_check")]
            panic!("double elimination");
        }
    }
}

#[cfg(feature = "best_phases_tracking")]
impl AssignStack {
    /// check usability of the saved best phase.
    /// return `true` if the current best phase got invalid.
    fn check_best_phase(&mut self, vi: VarId) -> bool {
        if let Some((b, _)) = self.best_phases.get(&vi) {
            debug_assert!(self.var[vi].assign.is_some());
            if self.var[vi].assign != Some(*b) {
                if self.root_level == self.var[vi].level {
                    self.best_phases.clear();
                    self.num_best_assign = self.num_asserted_vars + self.num_eliminated_vars;
                }
                return true;
            }
        }
        false
    }
}

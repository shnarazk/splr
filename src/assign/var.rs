/// Var struct and Database management API
use {
    super::{AssignStack, Var, VarHeapIF},
    crate::types::*,
    std::{
        fmt,
        slice::{Iter, IterMut},
    },
};

impl Default for Var {
    fn default() -> Var {
        Var {
            index: 0,
            participated: 0,
            reward: 0.0,
            timestamp: 0,
            flags: Flag::empty(),
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(
            f,
            "V{{{} {}{}}}",
            self.index,
            st(Flag::TOUCHED, ", touched"),
            st(Flag::ELIMINATED, ", eliminated"),
        )
    }
}

impl From<usize> for Var {
    #[inline]
    fn from(i: usize) -> Self {
        Var {
            index: i,
            ..Var::default()
        }
    }
}

impl Var {
    /// return a new vector of $n$ `Var`s.
    pub fn new_vars(n: usize) -> Vec<Var> {
        let mut vec = Vec::with_capacity(n + 1);
        for i in 0..=n {
            vec.push(Var::from(i));
        }
        vec
    }
    #[cfg(not(feature = "var_staging"))]
    pub fn activity(&self, _: f64) -> f64 {
        self.reward
    }
    #[cfg(feature = "var_staging")]
    pub fn activity(&self, extra: f64) -> f64 {
        let val = self.reward;
        if self.is(Flag::STAGED) {
            val + extra
        } else {
            val
        }
    }
}

impl FlagIF for Var {
    #[inline]
    fn is(&self, flag: Flag) -> bool {
        self.flags.contains(flag)
    }
    #[inline]
    fn set(&mut self, f: Flag, b: bool) {
        self.flags.set(f, b);
    }
    #[inline]
    fn turn_off(&mut self, flag: Flag) {
        self.flags.remove(flag);
    }
    #[inline]
    fn turn_on(&mut self, flag: Flag) {
        self.flags.insert(flag);
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
    /// eliminate a var.
    fn set_eliminated(&mut self, vi: VarId);
}

impl VarManipulateIF for AssignStack {
    fn assigned(&self, l: Lit) -> Option<bool> {
        match unsafe { self.assign.get_unchecked(l.vi()) } {
            Some(x) if !bool::from(l) => Some(!x),
            x => *x,
        }
    }
    #[inline]
    fn assign(&self, vi: VarId) -> Option<bool> {
        unsafe { *self.assign.get_unchecked(vi) }
    }
    #[inline]
    fn level(&self, vi: VarId) -> DecisionLevel {
        unsafe { *self.level.get_unchecked(vi) }
    }
    #[inline]
    fn reason(&self, vi: VarId) -> AssignReason {
        unsafe { *self.reason.get_unchecked(vi) }
    }
    #[inline]
    fn var(&self, vi: VarId) -> &Var {
        unsafe { self.var.get_unchecked(vi) }
    }
    #[inline]
    fn var_mut(&mut self, vi: VarId) -> &mut Var {
        unsafe { self.var.get_unchecked_mut(vi) }
    }
    fn var_iter(&self) -> Iter<'_, Var> {
        self.var.iter()
    }
    fn var_iter_mut(&mut self) -> IterMut<'_, Var> {
        self.var.iter_mut()
    }
    fn set_eliminated(&mut self, vi: VarId) {
        if !self.var[vi].is(Flag::ELIMINATED) {
            self.var[vi].turn_on(Flag::ELIMINATED);
            self.set_activity(vi, 0.0);
            self.remove_from_heap(vi);
            self.num_eliminated_vars += 1;
        } else {
            #[cfg(feature = "boundary_check")]
            panic!("double elimination");
        }
    }
}

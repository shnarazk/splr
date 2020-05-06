/// Var struct and Database management API
use {
    super::{AssignStack, ClauseManipulateIF, Var, VarRewardIF},
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
            reward: 0.0,
            timestamp: 0,
            flags: Flag::empty(),
            participated: 0,
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
    /// return the following data:
    /// * the number of vars
    /// * the number of solved vars
    /// * the number of eliminated vars
    /// * the number of unsolved vars
    fn var_stats(&self) -> (usize, usize, usize, usize);
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
            self.clear_reward(vi);
            self.num_eliminated_vars += 1;
        } else {
            #[cfg(feature = "boundary_check")]
            panic!("double elimination");
        }
    }
    #[inline]
    fn var_stats(&self) -> (usize, usize, usize, usize) {
        (
            self.num_vars,
            self.num_solved_vars,
            self.num_eliminated_vars,
            self.num_vars - self.num_solved_vars - self.num_eliminated_vars,
        )
    }
}

impl ClauseManipulateIF for AssignStack {
    fn satisfies(&self, vec: &[Lit]) -> bool {
        for l in vec {
            if self.assigned(*l) == Some(true) {
                return true;
            }
        }
        false
    }
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool {
        let lits = &c.lits;
        debug_assert!(1 < lits.len());
        let l0 = lits[0];
        self.assigned(l0) == Some(true)
            && matches!(self.reason(l0.vi()), AssignReason::Implication(x, _) if x == cid)
    }
}

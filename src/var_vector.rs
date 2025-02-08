#![allow(static_mut_refs)]
use crate::{types::*, vam::VarActivityManager};

pub static mut VAR_VECTOR: Vec<Var> = Vec::new();

pub trait VarRefIF {
    fn assign(&self) -> Option<bool>;
    fn set_assign(&self, value: Option<bool>);
    fn level(&self) -> DecisionLevel;
    fn set_level(&self, value: DecisionLevel);
    fn reason(&self) -> AssignReason;
    fn set_reason(&self, value: AssignReason);
    fn reason_saved(&self) -> AssignReason;
    fn set_reason_saved(&self, value: AssignReason);
    fn activity(&self) -> f64;
    fn set_activity(&self, value: f64);
    fn update_activity(&self, decay: f64, anti_decay: f64);
    fn is(&self, f: FlagVar) -> bool;
    fn turn_on(&self, f: FlagVar);
    fn turn_off(&self, f: FlagVar);
    fn set_flag(&self, f: FlagVar, b: bool);
}

pub struct VarRef(pub usize);

impl VarRef {
    // you can't call this function `Instantiate::instantiate`. It must return `Self`.
    pub fn instantiate(_config: &Config, cnf: &CNFDescription) {
        unsafe {
            let num_vars = cnf.num_of_variables;
            VAR_VECTOR.clear(); // reqired for cargo test
            VAR_VECTOR.resize(num_vars + 1, Var::default());
            for (i, v) in VAR_VECTOR.iter_mut().enumerate().skip(1) {
                v.level = i as DecisionLevel;
            }
        }
    }
    pub fn var_id_iter() -> impl Iterator<Item = VarId> {
        unsafe { (1..VAR_VECTOR.len()).map(|i| i as VarId) }
    }
    pub fn num_vars() -> usize {
        unsafe { VAR_VECTOR.len() - 1 }
    }
    pub fn add_var() {
        unsafe {
            VAR_VECTOR.push(Var::default());
        }
    }
    #[inline]
    pub fn lit_assigned(lit: Lit) -> Option<bool> {
        unsafe {
            let vi = lit.vi();
            let possitive = bool::from(lit);
            match VAR_VECTOR.get_unchecked(vi).assign {
                Some(b) if !possitive => Some(!b),
                ob => ob,
            }
        }
    }
    pub fn set_lit(lit: Lit) {
        unsafe {
            let vi = lit.vi();
            let possitive = bool::from(lit);
            VAR_VECTOR.get_unchecked_mut(vi).assign = Some(possitive);
        }
    }
    pub fn rescale_activity(scaling: f64) {
        unsafe {
            for i in VarRef::var_id_iter() {
                VAR_VECTOR.get_unchecked_mut(i).activity *= scaling;
            }
        }
    }
    /// set `vi`s status to asserted.
    pub fn make_var_asserted(vi: VarId) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(vi).reason = AssignReason::Decision(0);
            VAR_VECTOR.get_unchecked_mut(vi).activity = 0.0;
        }
        VarActivityManager::remove_from_heap(vi);

        #[cfg(feature = "boundary_check")]
        {
            VarRef(vi).timestamp = VAM.tick;
        }
    }
    /// set `vi`s status to eliminated.
    /// return true if `vi` is just eliminated.
    pub fn make_var_eliminated(vi: VarId) -> bool {
        unsafe {
            let v = VAR_VECTOR.get_unchecked_mut(vi);
            if v.is(FlagVar::ELIMINATED) {
                #[cfg(feature = "boundary_check")]
                panic!("double elimination");
                false
            } else {
                v.turn_on(FlagVar::ELIMINATED);
                v.activity = 0.0;
                VarActivityManager::remove_from_heap(vi);

                #[cfg(feature = "boundary_check")]
                {
                    v.timestamp = self.tick;
                }
                true
            }
        }
    }
}

impl VarRefIF for VarRef {
    #[inline]
    fn assign(&self) -> Option<bool> {
        unsafe { VAR_VECTOR.get_unchecked(self.0).assign }
    }
    #[inline]
    fn set_assign(&self, value: Option<bool>) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(self.0).assign = value;
        }
    }
    #[inline]
    fn level(&self) -> DecisionLevel {
        unsafe { VAR_VECTOR.get_unchecked(self.0).level }
    }
    #[inline]
    fn set_level(&self, value: DecisionLevel) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(self.0).level = value;
        }
    }
    #[inline]
    fn reason(&self) -> AssignReason {
        unsafe { VAR_VECTOR.get_unchecked(self.0).reason }
    }
    #[inline]
    fn set_reason(&self, value: AssignReason) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(self.0).reason = value;
        }
    }
    #[inline]
    fn reason_saved(&self) -> AssignReason {
        unsafe { VAR_VECTOR.get_unchecked(self.0).reason_saved }
    }
    #[inline]
    fn set_reason_saved(&self, value: AssignReason) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(self.0).reason_saved = value;
        }
    }
    #[inline]
    fn activity(&self) -> f64 {
        unsafe { VAR_VECTOR.get_unchecked(self.0).activity }
    }
    #[inline]
    fn set_activity(&self, value: f64) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(self.0).activity = value;
        }
    }
    #[inline]
    fn update_activity(&self, decay: f64, anti_decay: f64) {
        unsafe {
            VAR_VECTOR
                .get_unchecked_mut(self.0)
                .update_activity(decay, anti_decay);
        }
    }
    #[inline]
    fn is(&self, f: FlagVar) -> bool {
        unsafe { VAR_VECTOR.get_unchecked(self.0).flags.contains(f) }
    }
    #[inline]
    fn turn_on(&self, f: FlagVar) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(self.0).flags.insert(f);
        }
    }
    #[inline]
    fn turn_off(&self, f: FlagVar) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(self.0).flags.remove(f);
        }
    }
    #[inline]
    fn set_flag(&self, f: FlagVar, b: bool) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(self.0).flags.set(f, b);
        }
    }
}

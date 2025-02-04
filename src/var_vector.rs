#![allow(static_mut_refs)]
use crate::types::*;

pub static mut VAR_VECTOR: Vec<Var> = Vec::new();

pub trait VarRefIF {
    fn initialize(&self);
    fn add_var(&self);
    fn assign(&self) -> Option<bool>;
    fn assigned(&self, possitive: bool) -> Option<bool>;
    fn set_assign(&self, value: Option<bool>);
    fn level(&self) -> DecisionLevel;
    fn set_level(&self, value: DecisionLevel);
    fn reason(&self) -> AssignReason;
    fn set_reason(&self, value: AssignReason);
    fn reason_saved(&self) -> AssignReason;
    fn set_reason_saved(&self, value: AssignReason);
    fn reward(&self) -> f64;
    fn set_reward(&self, value: f64);
    fn update_activity(&self, decay: f64, anti_decay: f64);
    fn is(&self, f: FlagVar) -> bool;
    fn turn_on(&self, f: FlagVar);
    fn turn_off(&self, f: FlagVar);
    fn set_flag(&self, f: FlagVar, b: bool);
}

pub struct VarRef(pub usize);

impl VarRef {
    pub fn var_id_iter() -> impl Iterator<Item = VarId> {
        unsafe { (1..VAR_VECTOR.len()).map(|i| i as VarId) }
    }
    pub fn num_vars(&self) -> usize {
        unsafe { VAR_VECTOR.len() - 1 }
    }
}

impl VarRefIF for VarRef {
    fn initialize(&self) {
        unsafe {
            VAR_VECTOR.resize(self.0 + 1, Var::default());
        }
    }
    fn add_var(&self) {
        unsafe {
            VAR_VECTOR.push(Var::default());
        }
    }
    #[inline]
    fn assign(&self) -> Option<bool> {
        unsafe { VAR_VECTOR.get_unchecked(self.0).assign }
    }
    #[inline]
    fn assigned(&self, possitive: bool) -> Option<bool> {
        unsafe {
            match VAR_VECTOR.get_unchecked(self.0).assign {
                Some(b) if !possitive => Some(!b),
                ob => ob,
            }
        }
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
    fn reward(&self) -> f64 {
        unsafe { VAR_VECTOR.get_unchecked(self.0).reward }
    }
    #[inline]
    fn set_reward(&self, value: f64) {
        unsafe {
            VAR_VECTOR.get_unchecked_mut(self.0).reward = value;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_of_concept_of_static_mut() {
        VarRef(10).initialize();
    }
}

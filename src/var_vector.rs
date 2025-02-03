#![allow(static_mut_refs)]
use crate::types::*;

pub static mut VAR_VECTOR: Vec<Var> = Vec::new();

pub trait VarRefIF {
    fn initialize(&self);
    fn assign(&self) -> Option<bool>;
    fn set_assign(&self, value: Option<bool>);
    fn level(&self) -> DecisionLevel;
    fn set_level(&self, value: DecisionLevel);
    fn reason(&self) -> AssignReason;
    fn set_reason(&self, value: AssignReason);
    fn reason_saved(&self) -> AssignReason;
    fn set_reason_saved(&self, value: AssignReason);
    fn reward(&self) -> f64;
    fn set_reward(&self, value: f64);
}
pub struct VarRef(usize);

impl VarRefIF for VarRef {
    fn initialize(&self) {
        unsafe {
            VAR_VECTOR.truncate(self.0);
        }
    }
    fn assign(&self) -> Option<bool> {
        unsafe { VAR_VECTOR[self.0].assign }
    }
    fn set_assign(&self, value: Option<bool>) {
        unsafe {
            VAR_VECTOR[self.0].assign = value;
        }
    }
    fn level(&self) -> DecisionLevel {
        unsafe { VAR_VECTOR[self.0].level }
    }
    fn set_level(&self, value: DecisionLevel) {
        unsafe {
            VAR_VECTOR[self.0].level = value;
        }
    }
    fn reason(&self) -> AssignReason {
        unsafe { VAR_VECTOR[self.0].reason }
    }
    fn set_reason(&self, value: AssignReason) {
        unsafe {
            VAR_VECTOR[self.0].reason = value;
        }
    }
    fn reason_saved(&self) -> AssignReason {
        unsafe { VAR_VECTOR[self.0].reason_saved }
    }
    fn set_reason_saved(&self, value: AssignReason) {
        unsafe {
            VAR_VECTOR[self.0].reason_saved = value;
        }
    }
    fn reward(&self) -> f64 {
        unsafe { VAR_VECTOR[self.0].reward }
    }
    fn set_reward(&self, value: f64) {
        unsafe {
            VAR_VECTOR[self.0].reward = value;
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

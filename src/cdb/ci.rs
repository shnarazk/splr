use super::{ClauseIndex, Lit};

pub trait LiftedClauseIF {
    fn is_lifted(&self) -> bool;
    fn lift(lit: Lit) -> Self;
    fn unlift(&self) -> Lit;
}

pub trait DeadWatcherIF {
    fn is_dead(&self) -> bool;
    fn make_dead(&self) -> Self;
    fn extract(&self) -> Self;
}

const LIFT_MASK: usize = 0x4000_0000_0000_0000;
const DEAD_MASK: usize = 0x8000_0000_0000_0000;

impl LiftedClauseIF for ClauseIndex {
    fn is_lifted(&self) -> bool {
        0 != self & LIFT_MASK
    }
    fn lift(lit: Lit) -> Self {
        usize::from(lit) | LIFT_MASK
    }
    fn unlift(&self) -> Lit {
        Lit::from(*self & !LIFT_MASK)
    }
}

impl DeadWatcherIF for ClauseIndex {
    fn is_dead(&self) -> bool {
        0 != self & DEAD_MASK
    }
    fn make_dead(&self) -> Self {
        self | DEAD_MASK
    }
    fn extract(&self) -> Self {
        *self & !DEAD_MASK
    }
}

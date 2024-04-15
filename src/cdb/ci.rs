use super::{ClauseIndex, Lit};

pub trait LiftedClauseIF {
    fn is_lifted(&self) -> bool;
    fn lift(lit: Lit) -> Self;
    fn unlift(&self) -> Lit;
}

const MASK: usize = 0x8000_0000;

impl LiftedClauseIF for ClauseIndex {
    fn is_lifted(&self) -> bool {
        0 != self & MASK
    }
    fn lift(lit: Lit) -> Self {
        usize::from(lit) | MASK
    }
    fn unlift(&self) -> Lit {
        Lit::from(*self & !MASK)
    }
}

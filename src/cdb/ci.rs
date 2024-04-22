use super::{ClauseIndex, Lit};

pub trait LiftedClauseIF {
    fn is_lifted(&self) -> bool;
    fn lift(lit: Lit) -> Self;
    fn unlift(&self) -> Lit;
}

const MASK: usize = 0x8000_0000_0000_0000;
const U32BIT: usize = 0x0000_0000_FFFF_FFFF;

impl LiftedClauseIF for ClauseIndex {
    fn is_lifted(&self) -> bool {
        0 != self & MASK
    }
    fn lift(lit: Lit) -> Self {
        usize::from(lit) | MASK
    }
    fn unlift(&self) -> Lit {
        Lit::from(*self & U32BIT)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lift_unlift() {
        let lit = Lit::from(0x8FFF_FFFF_u32);
        assert_eq!(ClauseIndex::lift(lit).unlift(), lit);
    }
}

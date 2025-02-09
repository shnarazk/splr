//! Bounded static Var ref

use crate::{types::*, var_vector::*};

/// Bounded Static Var Ref
pub struct BSVR {
    pub var: &'static Var,
    pub vi: VarId,
    pub possitive: bool,
}

impl Default for BSVR {
    fn default() -> Self {
        BSVR {
            var: VarRef(0).get_reference(),
            vi: 0,
            possitive: true,
        }
    }
}

impl BSVR {
    pub fn new(vi: VarId, possitive: bool) -> Self {
        BSVR {
            var: VarRef(vi).get_reference(),
            vi,
            possitive,
        }
    }
    #[inline]
    pub fn lit_assigned(&self) -> Option<bool> {
        match self.var.assign {
            Some(b) if !self.possitive => Some(!b),
            ob => ob,
        }
    }
    pub fn as_lit(&self) -> Lit {
        Lit::from((self.vi, self.possitive))
    }
}

impl From<Lit> for BSVR {
    fn from(lit: Lit) -> Self {
        BSVR::new(lit.vi(), bool::from(lit))
    }
}

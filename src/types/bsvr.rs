//! Bounded static Var ref
#![allow(static_mut_refs)]

use {
    crate::{types::*, var_vector::*},
    std::{hash::Hash, ops::Not},
};

/// Bounded Static Var Ref
#[derive(Clone, Copy, Debug)]
pub struct BSVR {
    pub var: &'static Var,
    pub possitive: bool,
}

impl Default for BSVR {
    fn default() -> Self {
        BSVR {
            var: VarRef(0).get_reference(),
            possitive: true,
        }
    }
}

impl PartialEq for BSVR {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.var.id == other.var.id && self.possitive == other.possitive
    }
}

impl Eq for BSVR {}

impl PartialOrd for BSVR {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BSVR {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.var.id.cmp(&other.var.id)
    }
}

impl Hash for BSVR {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.var.id.hash(state);
        self.possitive.hash(state);
    }
}

impl BSVR {
    pub fn new(vi: VarId, possitive: bool) -> Self {
        BSVR {
            var: VarRef(vi).get_reference(),
            possitive,
        }
    }
    #[inline]
    pub fn lit_assigned(&self) -> Option<bool> {
        match self.var.assign {
            // |           | !b   |  b   |
            // |-----------|------|------|
            // |!possitive | true |false |
            // |possitive  | false| true |
            Some(b) => Some(b == self.possitive),
            ob => ob,
        }
    }
    #[inline]
    pub fn inject(&self) {
        VarRef(self.var.id).set_assign(Some(self.possitive));
    }
    #[inline]
    pub fn inject_level_and_reason(&self, lv: DecisionLevel, r: AssignReason) {
        unsafe {
            let v = VAR_VECTOR.get_unchecked_mut(self.var.id);
            v.assign = Some(self.possitive);
            v.level = lv;
            v.reason = r;
        }
    }
    #[inline]
    pub fn vi(&self) -> VarId {
        self.var.id
    }
    #[inline]
    pub fn as_lit(&self) -> Lit {
        Lit::from((self.var.id, self.possitive))
    }
}

impl From<Lit> for BSVR {
    fn from(lit: Lit) -> Self {
        BSVR::new(lit.vi(), bool::from(lit))
    }
}

impl From<BSVR> for Lit {
    fn from(l: BSVR) -> Lit {
        Lit::from((l.var.id, l.possitive))
    }
}

impl From<BSVR> for usize {
    fn from(l: BSVR) -> usize {
        l.var.id << 1 | (l.possitive as usize)
    }
}

impl From<BSVR> for i32 {
    fn from(l: BSVR) -> i32 {
        if l.possitive {
            l.var.id as i32
        } else {
            -(l.var.id as i32)
        }
    }
}

impl From<i32> for BSVR {
    fn from(i: i32) -> BSVR {
        if i > 0 {
            BSVR::new(i as VarId, true)
        } else {
            BSVR::new((-i) as VarId, false)
        }
    }
}

impl From<BSVR> for bool {
    fn from(l: BSVR) -> bool {
        l.possitive
    }
}

impl Not for BSVR {
    type Output = Self;
    fn not(self) -> Self::Output {
        BSVR {
            var: self.var,
            possitive: !self.possitive,
        }
    }
}

impl std::fmt::Display for BSVR {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}{}",
            if self.possitive { "" } else { "-" },
            self.var.id,
        )
    }
}

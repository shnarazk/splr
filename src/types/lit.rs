use {
    crate::types::var::Var,
    std::{fmt, ops::Not},
};

/// Literal as bounded Var
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lit<'a> {
    pub var: &'a Var<'a>,
    pub possitive: bool,
}

impl fmt::Display for Lit<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}L", i32::from(self))
    }
}

impl fmt::Debug for Lit<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}L", i32::from(self))
    }
}

/// convert literals to `[i32]` (for debug).
pub fn i32s(v: &[Lit<'_>]) -> Vec<i32> {
    v.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
}

impl<'a, 'b> From<(&'b Var<'a>, bool)> for Lit<'a>
where
    'b: 'a,
{
    /// make Lit from Var and value constraint (positive/negative)
    #[inline]
    fn from((var, possitive): (&'b Var<'a>, bool)) -> Self {
        Lit { var, possitive }
    }
}

impl<'a> TryFrom<&'a Var<'a>> for Lit<'a> {
    type Error = ();
    /// make Lit from Var and its value (positive/negative)
    #[inline]
    fn try_from(var: &'a Var<'a>) -> Result<Self, Self::Error> {
        if let Some(b) = var.assign {
            Ok(Lit { var, possitive: b })
        } else {
            Err(())
        }
    }
}

impl From<Lit<'_>> for bool {
    /// - positive Lit (= odd u32) => true
    /// - negative Lit (= even u32)  => false
    #[inline]
    fn from<'a>(l: Lit<'a>) -> bool {
        l.possitive
    }
}

impl From<Lit<'_>> for usize {
    /// return Literal encoding (2 * n +1 for possitive var n, 2 * n for negative var n)
    #[inline]
    fn from(l: Lit) -> usize {
        l.var.id << 1 | (l.possitive as usize)
    }
}

impl From<Lit<'_>> for i32 {
    #[inline]
    fn from(l: Lit) -> i32 {
        if l.possitive {
            l.var.id as i32
        } else {
            -(l.var.id as i32)
        }
    }
}

impl From<&Lit<'_>> for i32 {
    #[inline]
    fn from(l: &Lit) -> i32 {
        if l.possitive {
            l.var.id as i32
        } else {
            -(l.var.id as i32)
        }
    }
}

impl<'a> Not for Lit<'a> {
    type Output = Lit<'a>;
    #[inline]
    fn not(self) -> Self {
        Lit {
            var: self.var,
            possitive: !self.possitive,
        }
    }
}

impl<'a> Lit<'a> {
    /// return the assigned value from the view of lit.
    /// - `None` if the lit is not assigned.
    /// - `Some(true)` if the var is assigned to true and the lit is possitive.
    /// - `Some(false)` if the var is assigned to false and the lit is negative.
    pub fn assigned(&self) -> Option<bool> {
        self.var.assign.map(|a| if self.possitive { a } else { !a })
    }
}

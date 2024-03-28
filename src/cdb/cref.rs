use {
    super::{Clause, ClauseRef},
    std::{fmt, rc::Rc},
    // std::{fmt, sync::RwLock},
};

/// API for Clause Id.
pub trait ClauseRefIF {
    fn new(c: Clause) -> Self;
    fn get(&self) -> &Clause;
    fn get_mut(&mut self) -> &mut Clause;
    /// return `true` if a given clause id is made from a `Lit`.
    fn is_lifted_lit(&self) -> bool;
}

// impl Default for ClauseRef {
//     #[inline]
//     /// return the default empty clause, used in a reason slot or no conflict path.
//     fn default() -> Self {
//         ClauseRef {
//             ordinal: unsafe { NonZeroU32::new_unchecked(0x7FFF_FFFF) },
//         }
//     }
// }

// impl From<usize> for ClauseRef {
//     #[inline]
//     fn from(u: usize) -> ClauseRef {
//         ClauseRef {
//             ordinal: unsafe { NonZeroU32::new_unchecked(u as u32) },
//         }
//     }
// }

// impl From<ClauseRef> for usize {
//     #[inline]
//     fn from(cid: ClauseRef) -> usize {
//         NonZeroU32::get(cid.ordinal) as usize
//     }
// }

impl fmt::Debug for ClauseRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}C", self.c.lits)
    }
}

impl fmt::Display for ClauseRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}C", self.c.lits)
    }
}

impl ClauseRefIF for ClauseRef {
    fn new(c: Clause) -> Self {
        ClauseRef {
            c: Rc::new(Box::new(c)),
        }
    }
    fn get(&self) -> &Clause {
        &**self.c
    }
    fn get_mut(&mut self) -> &mut Clause {
        Rc::get_mut(&mut self.c).unwrap()
    }
    /// return `true` if the clause is generated from a literal by Eliminator.
    fn is_lifted_lit(&self) -> bool {
        unimplemented!("(**self.c).is_lifted_lit()")
        // 0 != 0x8000_0000 & NonZeroU32::get(self.ordinal)
    }
}

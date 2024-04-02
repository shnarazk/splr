use {
    super::Clause,
    std::{
        borrow::{Borrow, BorrowMut},
        cell::{Ref, RefCell},
        // cell::{Ref, RefCell, RefMut},
        fmt,
        rc::Rc,
        // sync::{LockResult, RwLock, RwLockReadGuard, RwLockWriteGuard},
    },
};

/// Clause identifier, or clause index, starting with one.
/// Note: ids are re-used after 'garbage collection'.
#[derive(Clone)]
pub struct ClauseRef {
    id: usize,
    c: Rc<RefCell<Clause>>,
}

impl PartialEq for ClauseRef {
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id)
    }
}

impl Eq for ClauseRef {}

impl std::hash::Hash for ClauseRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state)
    }
}

impl Ord for ClauseRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let c = self.get();
        let d = other.get();
        c.borrow().rank.cmp(&d.borrow().rank)
    }
}

impl PartialOrd for ClauseRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// API for Clause Id.
pub trait ClauseRefIF {
    fn new(id: usize, c: Clause) -> Self;
    // return shared reference
    fn get(&self) -> &RefCell<Clause>;
    // return mutable reference
    fn get_mut(&mut self) -> &mut RefCell<Clause>;
    /// return `true` if the clause is generated from a literal by Eliminator.
    fn is_lifted_lit(&self) -> bool;
}

impl ClauseRefIF for ClauseRef {
    fn new(id: usize, c: Clause) -> Self {
        ClauseRef {
            id,
            c: Rc::new(RefCell::new(c)),
        }
    }
    fn get(&self) -> &RefCell<Clause> {
        let r: Rc<RefCell<Clause>> = Rc::new(RefCell::new(1usize));
        let i: usize = *Borrow::<RefCell<usize>>::borrow(&r).borrow();
        self.c.borrow()
    }
    fn get_mut(&mut self) -> &mut RefCell<Clause> {
        self.c.borrow_mut()
    }
    /// return `true` if the clause is generated from a literal by Eliminator.
    fn is_lifted_lit(&self) -> bool {
        unimplemented!("(**self.c).is_lifted_lit()")
        // 0 != 0x8000_0000 & NonZeroU32::get(self.ordinal)
    }
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
        if let c = self.get() {
            write!(f, "{:?}C", c.borrow().lits)
        } else {
            write!(f, "?C")
        }
    }
}

impl fmt::Display for ClauseRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let c = self.get() {
            write!(f, "{:?}C", c.borrow().lits)
        } else {
            write!(f, "?C")
        }
    }
}

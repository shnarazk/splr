use {
    super::{Clause, Lit},
    crate::types::{FlagClause, FlagIF},
    std::{
        borrow::Borrow,
        cell::RefCell,
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
        // self.id.eq(&other.id)
        // let c = self.get();
        // let d = other.get();
        // c.eq(&d)
        Rc::ptr_eq(&self.c, &other.c)
    }
}

impl Eq for ClauseRef {}

impl std::hash::Hash for ClauseRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state)
        // let rcc = self.get();
        // let c = rcc.borrow();
        // c.hash(state)
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
    // // return mutable reference
    // fn get_mut(&self) -> RefCell<Clause>;
    /// return true if it is a lifted clause from a Lit
    fn is_lifted_lit(&self) -> bool;
    /// create a new lifted-clause
    fn lifted_clause_ref(l: Lit) -> Self;
    fn unlift(&self, c: &Clause) -> Lit;
}

impl ClauseRefIF for ClauseRef {
    fn new(id: usize, c: Clause) -> Self {
        ClauseRef {
            id,
            c: Rc::new(RefCell::new(c)),
        }
    }
    fn get(&self) -> &RefCell<Clause> {
        // let r: Rc<RefCell<usize>> = Rc::new(RefCell::new(1usize));
        // let i: usize = *Borrow::<RefCell<usize>>::borrow(&r).borrow();
        Borrow::<RefCell<Clause>>::borrow(&self.c)
    }
    // fn get_mut(&self) -> RefCell<Clause> {
    //     // let m = BorrowMut::<RefCell<Clause>>::borrow_mut(&mut self.c);
    //     // self.c.get_mut()
    //     Rc::into_inner(&self.c).unwrap()
    // }

    fn is_lifted_lit(&self) -> bool {
        self.id == 0
    }
    fn lifted_clause_ref(l: Lit) -> Self {
        let mut c = Clause::from(vec![l]);
        c.turn_on(FlagClause::LIT_CLAUSE);
        ClauseRef::new(0, c)
    }
    fn unlift(&self, c: &Clause) -> Lit {
        assert_eq!(self.id, 0);
        c.lits[0]
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
        let rcc = self.get();
        let c = rcc.borrow();
        write!(f, "{:?}C", c.lits)
    }
}

impl fmt::Display for ClauseRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let rcc = self.get();
        let c = rcc.borrow();
        write!(f, "{:?}C", c.lits)
    }
}

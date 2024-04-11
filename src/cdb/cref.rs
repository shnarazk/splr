use {
    super::Clause,
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
    c: Rc<RefCell<Clause>>,
}

impl PartialEq for ClauseRef {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.c, &other.c)
    }
}

impl Eq for ClauseRef {}

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
    fn new(c: Clause) -> Self;
    // return shared reference
    fn get(&self) -> &RefCell<Clause>;
}

impl ClauseRefIF for ClauseRef {
    fn new(c: Clause) -> Self {
        ClauseRef {
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
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assign::AssignStack, cdb::ClauseDB, types::*};

    #[test]
    fn cref_equality() {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut _asg = AssignStack::instantiate(&config, &cnf);
        let mut _cdb = ClauseDB::instantiate(&config, &cnf);
        let c = Clause::from(vec![Lit::from(1i32), Lit::from(2)]);
        let c1 = ClauseRef::new(c.clone());
        let c10 = c1.clone();
        let c11 = ClauseRef::new(c.clone());
        let c2 = ClauseRef::new(c.clone());
        assert!(c1 == c1);
        assert!(c1 == c10);
        assert!(c1 != c11);
        assert!(c1 != c2);
    }
    #[test]
    fn list_unlift() {
        for i in [1_i32, -1, 2, -2] {
            let l = Lit::from(i);
            let c = Clause::lift(l);
            let cr = ClauseRef::new(c);
            let rcc = cr.get();
            let c = rcc.borrow();
            assert_eq!(c.unlift(), l);
        }
    }
}

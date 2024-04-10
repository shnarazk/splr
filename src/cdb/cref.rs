use {
    super::Clause,
    std::{borrow::Borrow, cell::RefCell, fmt, rc::Rc},
};

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
        let rcc = Borrow::<RefCell<Clause>>::borrow(&self.c);
        let c = rcc.borrow();
        let rcd = Borrow::<RefCell<Clause>>::borrow(&other.c);
        let d = rcd.borrow();
        c.rank.cmp(&d.rank)
    }
}

impl PartialOrd for ClauseRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// API for Clause Id.
pub trait ClauseRefIF {
    /// return a new ClauseRef
    fn new(c: Clause) -> Self;
    /// return shared reference
    fn get(&self) -> &RefCell<Clause>;
}

impl ClauseRefIF for ClauseRef {
    fn new(c: Clause) -> Self {
        ClauseRef {
            c: Rc::new(RefCell::new(c)),
        }
    }
    fn get(&self) -> &RefCell<Clause> {
        Borrow::<RefCell<Clause>>::borrow(&self.c)
    }
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
    use super::super::*;
    use super::*;
    use crate::{assign::AssignStack, cdb::ClauseDB, types::*};

    fn lit(i: i32) -> Lit {
        Lit::from(i)
    }

    #[test]
    fn cref_equality() {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asg = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let cid = cdb
            .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false)
            .as_cid();
        let c = &cdb[cid];
        let c1 = ClauseRef::new(c.clone());
        let c10 = c1.clone();
        let c11 = ClauseRef::new(c.clone());
        let c2 = ClauseRef::new(c.clone());
        assert!(c1 == c1);
        assert!(c1 == c10);
        assert!(c1 != c11);
        assert!(c1 != c2);
    }
}

/// methods on `ClauseId`
mod cid;
/// methods on `Clause`
mod clause;
/// methods on `ClauseDB`
mod db;
/// methods about Literal Block Distance, or LBD
mod lbd;
/// methods on `Watch` and `WatchDB`
mod watch;

pub use self::{
    cid::ClauseIdIF,
    clause::ClauseIF,
    db::ClauseDBIF,
    lbd::LBDIF,
    watch::{Watch, WatchDBIF},
};

use crate::types::*;

/// Record of clause operations to build DRAT certifications.
#[derive(Debug, Eq, PartialEq)]
pub enum CertifiedRecord {
    /// placed at the end.
    SENTINEL,
    /// added a (learnt) clause.
    ADD,
    /// deleted a clause.
    DELETE,
}

type DRAT = Vec<(CertifiedRecord, Vec<i32>)>;

/// Clause identifier, or clause index, starting with one.
/// Note: ids are re-used after 'garbage collection'.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ClauseId {
    /// a sequence number.
    pub ordinal: u32,
}

impl ClauseId {
    #[inline]
    pub fn is_none(&self) -> bool {
        self.ordinal == 0
    }
}

/// A representation of 'clause'
#[derive(Debug)]
pub struct Clause {
    /// The literals in a clause.
    pub lits: Vec<Lit>,
    /// A static clause evaluation criterion like LBD, NDD, or something.
    pub rank: u16,
    /// the index from which `propagate` starts searching an unfalsified literal.
    pub search_from: usize,
    /// the last conflict at which this clause is used in conflict analysis.
    last_used: usize,
    /// A dynamic clause evaluation criterion based on the number of references.
    reward: f64,
    /// Flags
    flags: Flag,
}

/// Clause database
///
///```
/// use crate::{splr::config::Config, splr::types::*};
/// use crate::splr::cdb::ClauseDB;
/// let cdb = ClauseDB::instantiate(&Config::default(), &CNFDescription::default());
///```
#[derive(Debug)]
pub struct ClauseDB {
    /// container of clauses
    clause: Vec<Clause>,
    /// container of watch literals for binary clauses
    pub bin_watcher: Vec<Vec<Watch>>,
    /// container of watch literals
    pub watcher: Vec<Vec<Watch>>,
    /// clause history to make certification
    pub certified: DRAT,
    /// a number of clauses to emit out-of-memory exception
    soft_limit: usize,
    /// flag for Chan Seok heuristics; this value is exported with `Export:active_mode`
    use_chan_seok: bool,
    /// 'small' clause threshold
    co_lbd_bound: usize,
    // not in use
    // lbd_frozen_clause: usize,

    //
    //## Elimination
    //
    /// dirty literals
    touched: Vec<bool>,

    //
    //## LBD
    //
    /// a working buffer for LBD calculation
    lbd_temp: Vec<usize>,
    num_lbd_update: usize,

    //
    //## reduction
    //
    /// increment step of reduction threshold
    inc_step: usize,
    /// bonus step of reduction threshold used in good progress
    extra_inc: usize,
    first_reduction: usize,
    next_reduction: usize, // renamed from `nbclausesbeforereduce`
    reducable: bool,
    /// an expansion coefficient for restart
    reduction_coeff: usize,

    //
    //## statistics
    //
    /// the number of active (not DEAD) clauses.
    num_active: usize,
    /// the number of binary clauses.
    num_bi_clause: usize,
    /// the number of binary learnt clauses.
    num_bi_learnt: usize,
    /// the number of clauses which LBDs are 2.
    num_lbd2: usize,
    /// the present number of learnt clauses.
    num_learnt: usize,
    /// the number of reductions.
    num_reduction: usize,

    //
    //## vivification
    //
    pub during_vivification: bool,

    //
    //## incremental solving
    //
    pub eliminated_permanent: Vec<Vec<Lit>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assign::{AssignStack, PropagateIF};

    fn lit(i: i32) -> Lit {
        Lit::from(i)
    }

    #[allow(dead_code)]
    fn check_watches(cdb: &ClauseDB, cid: ClauseId) {
        let c = &cdb.clause[cid.ordinal as usize];
        if c.lits.is_empty() {
            println!("skip checking watches of an empty clause");
            return;
        }
        for l in &c.lits[0..=1] {
            let ws = &cdb.watcher[!*l];
            assert!(ws.iter().any(|w| w.c == cid));
        }
        println!("pass to check watches");
    }

    #[test]
    fn test_clause_instanciation() -> () {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asg = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        asg.assign_by_decision(lit(1));
        asg.assign_by_decision(lit(-2));

        let c1 = cdb.new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false, false);
        let c = &cdb[c1];
        assert_eq!(c.rank, 3);
        assert!(!c.is(Flag::DEAD));
        assert!(!c.is(Flag::LEARNT));
        assert!(!c.is(Flag::JUST_USED));

        let c2 = cdb.new_clause(&mut asg, &mut vec![lit(-1), lit(2), lit(3)], true, true);
        let c = &cdb[c2];
        assert_eq!(c.rank, 2);
        assert!(!c.is(Flag::DEAD));
        assert!(c.is(Flag::LEARNT));
        assert!(c.is(Flag::JUST_USED));
    }
    #[test]
    fn test_clause_equality() -> () {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asg = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let c1 = cdb.new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false, false);
        let c2 = cdb.new_clause(&mut asg, &mut vec![lit(-1), lit(4)], false, false);
        cdb[c2].reward = 0.0;
        assert_eq!(c1, c1);
        assert_eq!(c1 == c1, true);
        assert_ne!(c1, c2);
        assert_eq!(cdb.activity(c2), 0.0);
    }

    #[test]
    fn test_clause_iterator() -> () {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asg = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let c1 = cdb.new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false, false);
        assert_eq!(cdb[c1][0..].iter().map(|l| i32::from(*l)).sum::<i32>(), 6);
        let mut iter = cdb[c1][0..].into_iter();
        assert_eq!(iter.next(), Some(&lit(1)));
        assert_eq!(iter.next(), Some(&lit(2)));
        assert_eq!(iter.next(), Some(&lit(3)));
        assert_eq!(iter.next(), None);
    }
}

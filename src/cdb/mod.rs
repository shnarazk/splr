/// methods on clause activity
mod activity;
/// methods on binary link, namely binary clause
mod binary;
/// methods on `ClauseDB`
mod db;
/// EMA
mod ema;
/// methods for Stochastic Local Search
mod sls;
/// methods for UNSAT certification
mod unsat_certificate;
/// implementation of clause vivification
mod vivify;
/// types about watching literal
mod watch_cache;

pub use self::{
    binary::{BinaryLinkDB, BinaryLinkList},
    db::ClauseDB,
    property::*,
    sls::StochasticLocalSearchIF,
    unsat_certificate::CertificationStore,
    vivify::VivifyIF,
};

use {
    crate::{assign::AssignIF, types::*},
    std::{
        ops::IndexMut,
        slice::{Iter, IterMut},
    },
    watch_cache::{WatchCache, WatchCacheIterator, WatchCacheProxy},
};

#[cfg(not(feature = "no_IO"))]
use std::path::Path;

#[derive(Clone, Debug)]
pub enum ReductionType {
    /// weight by Reverse Activity Sum over the added clauses
    RASonADD(usize),
    /// weight by Reverse Activito Sum over all learnt clauses
    RASonALL(f64, f64),
    /// weight by Literal Block Distance over the added clauses
    LBDonADD(usize),
    /// weight by Literal Block Distance over all learnt clauses
    LBDonALL(u16, f64),
}

/// API for clause management like [`reduce`](`crate::cdb::ClauseDBIF::reduce`), [`new_clause`](`crate::cdb::ClauseDBIF::new_clause`), [`remove_clause`](`crate::cdb::ClauseDBIF::remove_clause`), and so on.
pub trait ClauseDBIF:
    Instantiate
    + IndexMut<ClauseId, Output = Clause>
    + PropertyDereference<property::Tusize, usize>
    + PropertyDereference<property::Tf64, f64>
{
    /// return the length of `clause`.
    fn len(&self) -> usize;
    /// return true if it's empty.
    fn is_empty(&self) -> bool;
    /// return an iterator.
    fn iter(&self) -> Iter<'_, Clause>;
    /// return a mutable iterator.
    fn iter_mut(&mut self) -> IterMut<'_, Clause>;

    //
    //## interface to binary links
    //

    /// return binary links: `BinaryLinkList` connected with a `Lit`.
    fn binary_links(&self, l: Lit) -> &BinaryLinkList;

    //
    //## abstraction to watch_cache
    //

    // get mutable reference to a watch_cache
    fn fetch_watch_cache_entry(&self, lit: Lit, index: WatchCacheProxy) -> (ClauseId, Lit);
    /// replace the mutable watcher list with an empty one, and return the list
    fn watch_cache_iter(&mut self, l: Lit) -> WatchCacheIterator;
    /// detach the watch_cache referred by the head of a watch_cache iterator
    fn detach_watch_cache(&mut self, l: Lit, iter: &mut WatchCacheIterator);
    /// Merge two watch cache
    fn merge_watch_cache(&mut self, l: Lit, wc: WatchCache);
    /// swap the first two literals in a clause.
    fn swap_watch(&mut self, cid: ClauseId);

    //
    //## clause transformation
    //

    /// push back a watch literal cache by adjusting the iterator for `lit`
    fn transform_by_restoring_watch_cache(
        &mut self,
        l: Lit,
        iter: &mut WatchCacheIterator,
        p: Option<Lit>,
    );
    /// swap i-th watch with j-th literal then update watch caches correctly
    fn transform_by_updating_watch(&mut self, cid: ClauseId, old: usize, new: usize, removed: bool);
    /// allocate a new clause and return its id.
    /// Note this removes an eliminated Lit `p` from a clause. This is an O(n) function!
    /// This returns `true` if the clause became a unit clause.
    /// And this is called only from `Eliminator::strengthen_clause`.
    fn new_clause(&mut self, asg: &mut impl AssignIF, v: &mut Vec<Lit>, learnt: bool) -> RefClause;
    fn new_clause_sandbox(&mut self, asg: &mut impl AssignIF, v: &mut Vec<Lit>) -> RefClause;
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn remove_clause(&mut self, cid: ClauseId);
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn remove_clause_sandbox(&mut self, cid: ClauseId);
    /// update watches of the clause
    fn transform_by_elimination(&mut self, cid: ClauseId, p: Lit) -> RefClause;
    /// generic clause transformer (not in use)
    fn transform_by_replacement(&mut self, cid: ClauseId, vec: &mut Vec<Lit>) -> RefClause;
    /// check satisfied and nullified literals in a clause
    fn transform_by_simplification(&mut self, asg: &mut impl AssignIF, cid: ClauseId) -> RefClause;
    /// reduce learnt clauses
    /// # CAVEAT
    /// *precondition*: decision level == 0.
    fn reduce(&mut self, asg: &mut impl AssignIF, setting: ReductionType);
    /// remove all learnt clauses.
    fn reset(&mut self);
    /// update flags.
    /// return `true` if it's learnt.
    fn update_at_analysis(&mut self, asg: &impl AssignIF, cid: ClauseId) -> bool;
    /// record an asserted literal to unsat certification.
    fn certificate_add_assertion(&mut self, lit: Lit);
    /// save the certification record to a file.
    fn certificate_save(&mut self);
    /// check the number of clauses
    /// * `Err(SolverError::OutOfMemory)` -- the db size is over the limit.
    /// * `Ok(true)` -- enough small
    /// * `Ok(false)` -- close to the limit
    fn check_size(&self) -> Result<bool, SolverError>;
    /// returns None if the given assignment is a model of a problem.
    /// Otherwise returns a clause which is not satisfiable under a given assignment.
    /// Clauses with an unassigned literal are treated as falsified in `strict` mode.
    fn validate(&self, model: &[Option<bool>], strict: bool) -> Option<ClauseId>;
    /// minimize a clause.
    fn minimize_with_bi_clauses(&mut self, asg: &impl AssignIF, vec: &mut Vec<Lit>);
    /// complete bi-clause network
    fn complete_bi_clauses(&mut self, asg: &mut impl AssignIF);

    //
    //## for debug
    //
    #[cfg(feature = "boundary_check")]
    /// return true if cid is included in watching literals
    fn watch_cache_contains(&self, lit: Lit, cid: ClauseId) -> bool;
    #[cfg(feature = "boundary_check")]
    /// return a clause's watches
    fn watch_caches(&self, cid: ClauseId, message: &str) -> (Vec<Lit>, Vec<Lit>);
    #[cfg(feature = "boundary_check")]
    fn is_garbage_collected(&mut self, cid: ClauseId) -> Option<bool>;
    #[cfg(not(feature = "no_IO"))]
    /// dump all active clauses and assertions as a CNF file.
    fn dump_cnf(&self, asg: &impl AssignIF, fname: &Path);
}

pub mod property {
    use super::ClauseDB;
    use crate::types::*;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Tusize {
        NumBiClause,
        NumBiClauseCompletion,
        NumBiLearnt,
        NumClause,
        NumLBD2,
        NumLearnt,
        NumReduction,
        NumReRegistration,
        Timestamp,
    }

    pub const USIZES: [Tusize; 9] = [
        Tusize::NumBiClause,
        Tusize::NumBiClauseCompletion,
        Tusize::NumBiLearnt,
        Tusize::NumClause,
        Tusize::NumLBD2,
        Tusize::NumLearnt,
        Tusize::NumReduction,
        Tusize::NumReRegistration,
        Tusize::Timestamp,
    ];

    impl PropertyDereference<Tusize, usize> for ClauseDB {
        #[inline]
        fn derefer(&self, k: Tusize) -> usize {
            match k {
                Tusize::NumClause => self.num_clause,
                Tusize::NumBiClause => self.num_bi_clause,
                Tusize::NumBiClauseCompletion => self.num_bi_clause_completion,
                Tusize::NumBiLearnt => self.num_bi_learnt,
                Tusize::NumLBD2 => self.num_lbd2,
                Tusize::NumLearnt => self.num_learnt,
                Tusize::NumReduction => self.num_reduction,
                Tusize::NumReRegistration => self.num_reregistration,

                #[cfg(feature = "clause_rewarding")]
                Tusize::Timestamp => self.tick,
                #[cfg(not(feature = "clause_rewarding"))]
                Tusize::Timestamp => 0,
            }
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Tf64 {
        LiteralBlockDistance,
        LiteralBlockEntanglement,
        ReductionThreshold,
    }

    pub const F64: [Tf64; 3] = [
        Tf64::LiteralBlockDistance,
        Tf64::LiteralBlockEntanglement,
        Tf64::ReductionThreshold,
    ];

    impl PropertyDereference<Tf64, f64> for ClauseDB {
        #[inline]
        fn derefer(&self, k: Tf64) -> f64 {
            match k {
                Tf64::LiteralBlockDistance => self.lbd.get(),
                Tf64::LiteralBlockEntanglement => self.lb_entanglement.get(),
                Tf64::ReductionThreshold => self.reduction_threshold,
            }
        }
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    pub enum TEma {
        Entanglement,
        LBD,
    }

    pub const EMAS: [TEma; 2] = [TEma::Entanglement, TEma::LBD];

    impl PropertyReference<TEma, EmaView> for ClauseDB {
        #[inline]
        fn refer(&self, k: TEma) -> &EmaView {
            match k {
                TEma::Entanglement => self.lb_entanglement.as_view(),
                TEma::LBD => self.lbd.as_view(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::*,
        crate::{
            assign::{AssignStack, PropagateIF},
            var_vector::*,
        },
        std::num::NonZeroU32,
    };

    fn lit(i: i32) -> Lit {
        Lit::from(i)
    }

    #[allow(dead_code)]
    fn check_watches(cdb: &ClauseDB, cid: ClauseId) {
        let c = &cdb.clause[NonZeroU32::get(cid.ordinal) as usize];
        if c.lits.is_empty() {
            println!("skip checking watches of an empty clause");
            return;
        }
        assert!(c.lits[0..2]
            .iter()
            .all(|l| cdb.watch_cache[!*l].iter().any(|(c, _)| *c == cid)));
        println!("pass to check watches");
    }

    #[test]
    fn test_clause_instantiation() {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        VarRef::initialize(4);
        assert_eq!(VarRef(1).level(), 1);
        assert_eq!(VarRef(4).level(), 4);
        let mut asg = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        // Now `asg.level` = [_, 1, 2, 3, 4, 5, 6].
        let c0 = cdb
            .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3), lit(4)], false)
            .as_cid();
        assert_eq!(cdb[c0].len(), 4);
        assert_eq!(cdb[c0].lit0().vi(), 1);
        assert_eq!(VarRef(cdb[c0].lit0().vi()).level(), 1);
        assert_eq!(VarRef(cdb[c0].lit0().vi()).assign(), None);
        assert_eq!(cdb[c0].rank, 4);

        asg.assign_by_decision(lit(-2)); // at level 1
        asg.assign_by_decision(lit(1)); // at level 2
                                        // Now `asg.level` = [_, 2, 1, 3, 4, 5, 6].
        let c1 = cdb
            .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false)
            .as_cid();
        let c = &cdb[c1];

        assert_eq!(c.rank, 3);
        assert!(!c.is_dead());
        assert!(!c.is(FlagClause::LEARNT));
        #[cfg(feature = "just_used")]
        assert!(!c.is(Flag::USED));
        let c2 = cdb
            .new_clause(&mut asg, &mut vec![lit(-1), lit(2), lit(3)], true)
            .as_cid();
        let c = &cdb[c2];
        assert_eq!(c.rank, 3);
        assert!(!c.is_dead());
        assert!(c.is(FlagClause::LEARNT));
        #[cfg(feature = "just_used")]
        assert!(!c.is(Flag::USED));
    }
    #[test]
    fn test_clause_equality() {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asg = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let c1 = cdb
            .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false)
            .as_cid();
        let c2 = cdb
            .new_clause(&mut asg, &mut vec![lit(-1), lit(4)], false)
            .as_cid();
        // cdb[c2].reward = 2.4;
        assert_eq!(c1, c1);
        assert_ne!(c1, c2);
        // assert_eq!(cdb.activity(c2), 2.4);
    }

    #[test]
    fn test_clause_iterator() {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asg = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let c1 = cdb
            .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false)
            .as_cid();
        assert_eq!(cdb[c1][0..].iter().map(|l| i32::from(*l)).sum::<i32>(), 6);
        let mut iter = cdb[c1][0..].iter();
        assert_eq!(iter.next(), Some(&lit(1)));
        assert_eq!(iter.next(), Some(&lit(2)));
        assert_eq!(iter.next(), Some(&lit(3)));
        assert_eq!(iter.next(), None);
    }
}

/// methods on `ClauseId`
mod cid;
/// methods on `Clause`
mod clause;
/// methods on `ClauseDB`
mod db;
/// methods for UNSAT certification
mod unsat_certificate;
/// types about watching literal
mod watch_cache;

pub use self::{cid::ClauseIdIF, property::*, unsat_certificate::CertificationStore};

use {
    crate::{assign::AssignIF, types::*},
    std::{
        num::NonZeroU32,
        ops::IndexMut,
        slice::{Iter, IterMut},
    },
    watch_cache::*,
};

/// API for Clause, providing literal accessors.
pub trait ClauseIF {
    /// return true if it contains no literals; a clause after unit propagation.
    fn is_empty(&self) -> bool;
    /// return true if it contains no literals; a clause after unit propagation.
    fn is_dead(&self) -> bool;
    /// return 1st watch
    fn lit0(&self) -> Lit;
    /// return 2nd watch
    fn lit1(&self) -> Lit;
    /// return `true` if the clause contains the literal
    fn contains(&self, lit: Lit) -> bool;
    /// check clause satisfiability
    fn is_satisfied_under<A>(&self, asg: &A) -> bool
    where
        A: AssignIF;
    /// return an iterator over its literals.
    fn iter(&self) -> Iter<'_, Lit>;
    /// return the number of literals.
    fn len(&self) -> usize;
    /// return timestamp
    fn timestamp(&self) -> usize;
    /// return `true` if the clause should try vivification
    fn to_vivify(&self, threshold: usize) -> Option<f64>;
    /// clear flags about vivification
    fn vivified(&mut self);

    #[cfg(feature = "boundary_check")]
    fn set_birth(&mut self, time: usize);
}

/// API for clause management like [`reduce`](`crate::cdb::ClauseDBIF::reduce`), [`new_clause`](`crate::cdb::ClauseDBIF::new_clause`), [`remove_clause`](`crate::cdb::ClauseDBIF::remove_clause`), and so on.
pub trait ClauseDBIF:
    ActivityIF<ClauseId>
    + IndexMut<ClauseId, Output = Clause>
    + Instantiate
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
    /// return a watcher list for bi-clauses
    fn bi_clause_map(&self, l: Lit) -> &BiClause;

    //
    //## abstraction to watch_cache
    //

    // get mutable reference to a watch_cache
    fn fetch_watch_cache_entry(&self, lit: Lit, index: WatchCacheProxy) -> (ClauseId, Lit);
    /// replace the mutable watcher list with an empty one, and return the list
    fn watch_cache_iter(&mut self, l: Lit) -> WatchCacheIterator;
    /// detach the watch_cache referred by the head of a watch_cache iterator
    fn detach_watch_cache(&mut self, l: Lit, iter: &mut WatchCacheIterator);
    /// register the clause to the previous watch cache
    fn reregister_watch_cache(&mut self, l: Lit, target: Option<WatchCacheProxy>);
    /// restore detached watch cache
    fn restore_detached_watch_cache(&mut self, l: Lit, wi: WatchCacheIterator);
    /// Merge two watch cache
    fn merge_watch_cache(&mut self, l: Lit, wc: WatchCache);
    /// swap the first two literals in a clause.
    fn swap_watch(&mut self, cid: ClauseId);

    //
    //## clause transformation
    //

    /// TODO
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
    fn new_clause<A>(&mut self, asg: &mut A, v: &mut Vec<Lit>, learnt: bool) -> RefClause
    where
        A: AssignIF;
    fn new_clause_sandbox<A>(&mut self, asg: &mut A, v: &mut Vec<Lit>) -> RefClause
    where
        A: AssignIF;
    /// remove a clause temporally
    fn detach_clause(&mut self, cid: ClauseId) -> (Lit, Lit);
    /// push back a clause
    fn reattach_clause(&mut self, cid: ClauseId, watches: (Lit, Lit));
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn remove_clause(&mut self, cid: ClauseId);
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn remove_clause_sandbox(&mut self, cid: ClauseId);
    /// update watches of the clause
    fn transform_by_elimination(&mut self, cid: ClauseId, p: Lit) -> RefClause;
    /// generic clause transformer (not in use)
    fn transform_by_replacement(&mut self, cid: ClauseId, vec: &mut Vec<Lit>) -> RefClause;
    /// check satisfied and nullified literals in a clause
    fn transform_by_simplification<A>(&mut self, asg: &mut A, cid: ClauseId) -> RefClause
    where
        A: AssignIF;
    /// check the condition to reduce.
    /// * return `true` if reduction is done.
    /// * Otherwise return `false`.
    ///
    /// # CAVEAT
    /// *precondition*: decision level == 0.
    fn reduce<A>(&mut self, asg: &mut A, nc: usize) -> bool
    where
        A: AssignIF;
    fn reset(&mut self);
    /// update LBD then convert a learnt clause to permanent if needed.
    fn mark_clause_as_used<A>(&mut self, asg: &mut A, cid: ClauseId) -> bool
    where
        A: AssignIF;
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
    fn minimize_with_bi_clauses<A>(&mut self, asg: &A, vec: &mut Vec<Lit>)
    where
        A: AssignIF;
    /// complete bi-clause network
    fn complete_bi_clauses<A>(&mut self, asg: &mut A)
    where
        A: AssignIF;

    #[cfg(feature = "incremental_solver")]
    /// save an eliminated permanent clause to an extra space for incremental solving.
    fn make_permanent_immortal(&mut self, cid: ClauseId);

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
    #[cfg(feature = "boundary_check")]
    fn check_consistency<A>(&mut self, asg: &A)
    where
        A: AssignIF;
}

/// Clause identifier, or clause index, starting with one.
/// Note: ids are re-used after 'garbage collection'.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ClauseId {
    /// a sequence number.
    pub ordinal: NonZeroU32,
}

/// A representation of 'clause'
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Clause {
    /// The literals in a clause.
    lits: Vec<Lit>,
    /// A static clause evaluation criterion like LBD, NDD, or something.
    pub rank: u16,
    /// the index from which `propagate` starts searching an un-falsified literal.
    pub search_from: usize,
    /// A dynamic clause evaluation criterion based on the number of references.
    reward: f64,
    /// the number of conflicts at which this clause was used in `conflict_analyze`
    timestamp: usize,
    /// Flags
    flags: Flag,

    #[cfg(feature = "boundary_check")]
    pub birth: usize,
    #[cfg(feature = "boundary_check")]
    pub moved_at: Propagate,
}

/// Clause database
///
///```
/// use crate::{splr::config::Config, splr::types::*};
/// use crate::splr::cdb::ClauseDB;
/// let cdb = ClauseDB::instantiate(&Config::default(), &CNFDescription::default());
///```
#[derive(Clone, Debug)]
pub struct ClauseDB {
    /// container of clauses
    clause: Vec<Clause>,
    /// hashed representation of binary clauses.
    ///## Note
    /// This means a biclause [l0, l1] is stored at bi_clause[l0] instead of bi_clause[!l0].
    ///
    pub bi_clause: Vec<BiClause>,
    /// container of watch literals
    pub watch_cache: Vec<WatchCache>,
    freelist: Vec<ClauseId>,
    certification_store: CertificationStore,
    /// a number of clauses to emit out-of-memory exception
    soft_limit: usize,
    /// flag for Chan Seok heuristics; this value is exported with `Export:mode`
    use_chan_seok: bool,
    /// 'small' clause threshold
    co_lbd_bound: u16,
    // not in use
    // lbd_frozen_clause: usize,

    // bi-clause completion
    bi_clause_completion_queue: Vec<Lit>,
    num_bi_clause_completion: usize,

    //
    //## clause rewarding
    //
    /// an index for counting elapsed time
    ordinal: usize,
    activity_decay: f64,
    activity_anti_decay: f64,
    activity_ema: Ema,

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
    reducible: bool,
    /// an expansion coefficient for restart
    reduction_coeff: usize,

    //
    //## statistics
    //
    /// the number of active (not DEAD) clauses.
    num_clause: usize,
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
    /// the number of reregistration of a bi-clause
    num_reregistration: usize,
    /// EMA of LBD of clauses used in conflict analysis (dependency graph)
    pub lbd_of_dp_ema: Ema,

    //
    //## incremental solving
    //
    pub eliminated_permanent: Vec<Vec<Lit>>,
}

pub mod property {
    use super::ClauseDB;
    use crate::types::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
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
                Tusize::Timestamp => self.ordinal,
            }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Tf64 {
        DpAverageLBD,
    }

    pub const F64: [Tf64; 1] = [Tf64::DpAverageLBD];

    impl PropertyDereference<Tf64, f64> for ClauseDB {
        #[inline]
        fn derefer(&self, k: Tf64) -> f64 {
            match k {
                Tf64::DpAverageLBD => self.lbd_of_dp_ema.get(),
            }
        }
    }
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
        let c = &cdb.clause[std::num::NonZeroU32::get(cid.ordinal) as usize];
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
    fn test_clause_instantiation() -> () {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asg = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        asg.assign_by_decision(lit(1));
        asg.assign_by_decision(lit(-2));

        let c1 = cdb
            .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false)
            .as_cid();
        let c = &cdb[c1];
        assert_eq!(c.rank, 2);
        assert!(!c.is_dead());
        assert!(!c.is(Flag::LEARNT));
        #[cfg(feature = "just_used")]
        assert!(!c.is(Flag::JUST_USED));

        let c2 = cdb
            .new_clause(&mut asg, &mut vec![lit(-1), lit(2), lit(3)], true)
            .as_cid();
        let c = &cdb[c2];
        assert_eq!(c.rank, 2);
        assert!(!c.is_dead());
        assert!(c.is(Flag::LEARNT));
        #[cfg(feature = "just_used")]
        assert!(!c.is(Flag::JUST_USED));
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
        let c1 = cdb
            .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false)
            .as_cid();
        let c2 = cdb
            .new_clause(&mut asg, &mut vec![lit(-1), lit(4)], false)
            .as_cid();
        cdb[c2].reward = 2.4;
        assert_eq!(c1, c1);
        assert_eq!(c1 == c1, true);
        assert_ne!(c1, c2);
        assert_eq!(cdb.activity(c2), 2.4);
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
        let c1 = cdb
            .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false)
            .as_cid();
        assert_eq!(cdb[c1][0..].iter().map(|l| i32::from(*l)).sum::<i32>(), 6);
        let mut iter = cdb[c1][0..].into_iter();
        assert_eq!(iter.next(), Some(&lit(1)));
        assert_eq!(iter.next(), Some(&lit(2)));
        assert_eq!(iter.next(), Some(&lit(3)));
        assert_eq!(iter.next(), None);
    }
}

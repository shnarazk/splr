/// methods on clause activity
mod activity;
/// methods on binary link, namely binary clause
mod binary;
/// methods on `ClauseIndex`
mod ci;
/// methods on `Clause`
mod clause;
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
/// methods on Watchers
mod weaver;

pub use self::{
    binary::{BinaryLinkDB, BinaryLinkList},
    ci::LiftedClauseIF,
    clause::*,
    db::ClauseDB,
    property::*,
    sls::StochasticLocalSearchIF,
    unsat_certificate::CertificationStore,
    vivify::VivifyIF,
    weaver::*,
};

use {
    self::binary::BinaryLinkIF,
    crate::{assign::AssignIF, types::*},
    ema::ProgressLBD,
    std::{
        collections::HashSet,
        ops::IndexMut,
        slice::{Iter, IterMut},
    },
};

#[cfg(not(feature = "no_IO"))]
use std::{io::Write, path::Path};

/// API for clause management like [`reduce`](`crate::cdb::ClauseDBIF::reduce`), [`new_clause`](`crate::cdb::ClauseDBIF::new_clause`) and so on.
pub trait ClauseDBIF:
    Instantiate
    + IndexMut<ClauseIndex, Output = Clause>
    + ClauseWeaverIF
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
    //## clause transformation
    //

    /// swap i-th watch with j-th literal then update watch caches correctly
    fn transform_by_updating_watch(
        &mut self,
        prev: ClauseIndex,
        ci: ClauseIndex,
        old: usize,
        new: usize,
    ) -> ClauseIndex;
    /// allocate a new clause and return its id.
    /// Note this removes an eliminated Lit `p` from a clause. This is an O(n) function!
    /// This returns `true` if the clause became a unit clause.
    /// And this is called only from `Eliminator::strengthen_clause`.
    fn new_clause(&mut self, asg: &mut impl AssignIF, v: &mut Vec<Lit>, learnt: bool) -> RefClause;
    fn new_clause_sandbox(&mut self, asg: &mut impl AssignIF, v: &mut Vec<Lit>) -> RefClause;
    fn transform_by_elimination(&mut self, ci: ClauseIndex, p: Lit) -> RefClause;
    /// generic clause transformer (not in use)
    fn transform_by_replacement(&mut self, ci: ClauseIndex, vec: &mut Vec<Lit>) -> RefClause;
    /// check satisfied and nullified literals in a clause
    fn transform_by_simplification(
        &mut self,
        asg: &mut impl AssignIF,
        ci: ClauseIndex,
        deads: &mut HashSet<Lit>,
    ) -> RefClause;
    /// reduce learnt clauses
    /// # CAVEAT
    /// *precondition*: decision level == 0.
    fn reduce(&mut self, asg: &mut impl AssignIF, setting: ReductionType);
    /// remove all learnt clauses.
    fn reset(&mut self);
    /// update flags.
    /// return `true` if it's learnt.
    fn update_at_analysis(&mut self, asg: &impl AssignIF, ci: ClauseIndex) -> bool;
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
    fn validate(&self, model: &[Option<bool>], strict: bool) -> Option<ClauseIndex>;
    /// minimize a clause.
    fn minimize_with_bi_clauses(&mut self, asg: &impl AssignIF, vec: &mut Vec<Lit>);
    /// complete bi-clause network
    fn complete_bi_clauses(&mut self, asg: &mut impl AssignIF);
    /// FIXME:
    fn preppend_clauses(&mut self, force: bool);

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
    #[cfg(not(feature = "no_IO"))]
    /// dump all active clauses and assertions as a CNF file.
    fn dump_cnf(&self, asg: &impl AssignIF, fname: &Path);
}

impl Default for ClauseDB {
    fn default() -> ClauseDB {
        ClauseDB {
            clause: Vec::new(),
            binary_link: BinaryLinkDB::default(),
            watch: Vec::new(),
            certification_store: CertificationStore::default(),
            soft_limit: 0, // 248_000_000
            co_lbd_bound: 4,
            preppend_head: true,

            bi_clause_completion_queue: Vec::new(),
            num_bi_clause_completion: 0,
            // lbd_frozen_clause: 30,
            #[cfg(feature = "clause_rewarding")]
            tick: 0,
            #[cfg(feature = "clause_rewarding")]
            activity_decay: 0.99,
            #[cfg(feature = "clause_rewarding")]
            activity_anti_decay: 0.01,

            lbd_temp: Vec::new(),
            lbd: ProgressLBD::default(),

            num_clause: 0,
            num_bi_clause: 0,
            num_bi_learnt: 0,
            num_lbd2: 0,
            num_learnt: 0,
            num_reduction: 0,
            num_reregistration: 0,
            lb_entanglement: Ema2::new(1_000).with_slow(80_000).with_value(2.0),
            reduction_threshold: 0.0,

            #[cfg(not(feature = "no_clause_elimination"))]
            eliminated_permanent: Vec::new(),
        }
    }
}

impl ClauseDBIF for ClauseDB {
    fn len(&self) -> usize {
        self.clause.len()
    }
    fn is_empty(&self) -> bool {
        self.clause.is_empty()
    }
    fn iter(&self) -> Iter<'_, Clause> {
        self.clause.iter()
    }
    fn iter_mut(&mut self) -> IterMut<'_, Clause> {
        self.clause.iter_mut()
    }
    #[inline]
    fn binary_links(&self, l: Lit) -> &BinaryLinkList {
        self.binary_link.connect_with(l)
    }
    fn new_clause(
        &mut self,
        asg: &mut impl AssignIF,
        vec: &mut Vec<Lit>,
        learnt: bool,
    ) -> RefClause {
        debug_assert!(1 < vec.len());
        // debug_assert!(vec.iter().all(|l| !vec.contains(&!*l)), "{vec:?}");
        if vec.len() == 2 {
            if let Some(&ci) = self.link_to_cid(vec[0], vec[1]) {
                self.num_reregistration += 1;
                return RefClause::RegisteredClause(ci);
            }
        }
        self.certification_store.add_clause(vec);
        let ci = self.get_free_index();
        self[ci].flags = FlagClause::empty();
        std::mem::swap(&mut self[ci].lits, vec);
        let len2 = self[ci].lits.len() == 2;
        let l0 = self[ci].lits[0];
        let l1 = self[ci].lits[1];
        if len2 {
            self[ci].rank = 1;
            // A binary clause consumes one clause without watchers
            self.num_bi_clause += 1;
            self.binary_link.add(l0, l1, ci);

            #[cfg(feature = "bi_clause_completion")]
            if learnt {
                for lit in c.iter() {
                    if !self.bi_clause_completion_queue.contains(lit) {
                        self.bi_clause_completion_queue.push(*lit);
                    }
                }
            }
        } else {
            self[ci].update_lbd(asg);
            self[ci].search_from = 0;
            self.insert_watcher(ci, false, !l0);
            self.insert_watcher(ci, true, !l1);
        }
        self[ci].rank_old = self[ci].rank;
        self.lbd.update(self[ci].rank);
        self.num_clause += 1;
        if learnt {
            if len2 {
                self.num_bi_learnt += 1;
            } else {
                self[ci].turn_on(FlagClause::LEARNT);
                self.num_learnt += 1;
                if self[ci].rank <= 2 {
                    self.num_lbd2 += 1;
                }
            }
        }

        #[cfg(feature = "clause_rewarding")]
        {
            self[ci].reward = 0.0;
            self[ci].timestamp = *tick;
        }
        RefClause::Clause(ci)
    }

    fn new_clause_sandbox(&mut self, asg: &mut impl AssignIF, vec: &mut Vec<Lit>) -> RefClause {
        debug_assert!(1 < vec.len());
        if vec.len() == 2 {
            if let Some(&ci) = self.link_to_cid(vec[0], vec[1]) {
                return RefClause::RegisteredClause(ci);
            }
        }
        let ci = self.get_free_index();
        // let c = &mut self[ci];
        self[ci].flags = FlagClause::empty();
        std::mem::swap(&mut self[ci].lits, vec);
        let len2 = self[ci].lits.len() == 2;
        let l0 = self[ci].lits[0];
        let l1 = self[ci].lits[1];
        if len2 {
            self[ci].rank = 1;
            self.binary_link.add(l0, l1, ci);
        } else {
            self[ci].search_from = 0;
            self[ci].update_lbd(asg);
            self[ci].turn_on(FlagClause::LEARNT);
            self.insert_watcher(ci, false, !l0);
            self.insert_watcher(ci, true, !l1);
        }
        self[ci].rank_old = self[ci].rank;

        #[cfg(feature = "clause_rewarding")]
        {
            self[ci].timestamp = *tick;
        }
        RefClause::Clause(ci)
    }

    //
    // return a Lit if the clause becomes a unit clause.
    fn transform_by_elimination(&mut self, ci: ClauseIndex, p: Lit) -> RefClause {
        //
        //## Clause transform rules
        //
        // There are four cases:
        // 1. a bi-clause becomes a unit clause.                   [Case:2-1]
        // 2. a normal clause is merged to a registered bi-clause. [Case:3-0]
        // 3. a normal clause becomes a new bi-clause.             [Case:3-2]
        // 4. a normal clause becomes a shorter normal clause.     [Case:3-3]
        //

        // self.watches(cid, "before strengthen_by_elimination");
        debug_assert!(!self[ci].is_dead());
        debug_assert!(1 < self[ci].len());
        // let ClauseDB {
        //     ref mut clause,
        //     ref mut binary_link,
        //     ref mut certification_store,
        //     ref mut num_bi_clause,
        //     ..
        // } = self;
        // let c = &mut self.clause[ci];
        // debug_assert!((*ch).lits.contains(&p));
        // debug_assert!(1 < (*ch).len());
        debug_assert!(1 < usize::from(!p));
        // let lits = &mut self[ci].lits;
        debug_assert!(1 < self[ci].lits.len());
        //
        //## Case:2-0
        //
        if self[ci].lits.len() == 2 {
            if self[ci].lits[0] == p {
                self[ci].lits.swap(0, 1);
            }
            return RefClause::UnitClause(self[ci].lits[0]);
        }

        self[ci].search_from = 0;
        let mut new_lits: Vec<Lit> = self[ci]
            .lits
            .iter()
            .filter(|&l| *l != p)
            .copied()
            .collect::<Vec<Lit>>();
        if new_lits.len() == 2 {
            if let Some(&reg) = self.binary_link.search(new_lits[0], new_lits[1]) {
                //
                //## Case:3-0
                //
                return RefClause::RegisteredClause(reg);
            }
            //
            //## Case:3-2
            //
            // let l0 = self[ci].lits[0];
            // let l1 = self[ci].lits[1];
            // watch_cache[!l0].remove_watch(&ci);
            // watch_cache[!l1].remove_watch(&ci);
            self.remove_watcher(ci);
            std::mem::swap(&mut self[ci].lits, &mut new_lits);
            self.binary_link.add(self[ci].lits[0], self[ci].lits[1], ci);
            self.num_bi_clause += 1;
            // self.watches(cid, "after strengthen_by_elimination case:3-2");
        } else {
            //
            //## Case:3-3
            //
            // let old_l0 = self[ci].lits[0];
            // let old_l1 = self[ci].lits[1];
            self.remove_watcher(ci);
            std::mem::swap(&mut self[ci].lits, &mut new_lits);
            let l0 = self[ci].lits[0];
            let l1 = self[ci].lits[1];
            self.insert_watcher(ci, false, !l0);
            self.insert_watcher(ci, true, !l1);
            /*
            // Here we assumed that there's no eliminated var in clause and *watch cache*.
            // Fortunately the current implementation purges all eliminated vars fully.
            if p == old_l0 {
                // watch_cache[!p].remove_watch(&ci);
                let second = self.remove_watcher(ci, !p);
                if old_l1 == l0 {
                    // debug_assert!(watch_cache[!l1].iter().all(|e| e.0 != ci));
                    // watch_cache[!l1].insert_watch(ci, l0);
                    self.insert_watcher(ci, second, !l1);
                } else if old_l1 == l1 {
                    // debug_assert!(watch_cache[!l0].iter().all(|e| e.0 != ci));
                    // watch_cache[!l0].insert_watch(ci, l1);
                    self.insert_watcher(ci, second, !l0);
                } else {
                    unreachable!("transform_by_elimination");
                }
            } else if p == old_l1 {
                // watch_cache[!p].remove_watch(&ci);
                let second = self.remove_watcher(ci, !p);
                if old_l0 == l0 {
                    // debug_assert!(watch_cache[!l1].iter().all(|e| e.0 != ci));
                    // watch_cache[!l1].insert_watch(ci, l0);
                    self.insert_watcher(ci, second, !l1);
                } else if old_l0 == l1 {
                    // debug_assert!(watch_cache[!l0].iter().all(|e| e.0 != ci));
                    // watch_cache[!l0].insert_watch(ci, l1);
                    self.insert_watcher(ci, second, !l0);
                } else {
                    unreachable!("transform_by_elimination");
                }
            } else {
                debug_assert_eq!(old_l0, l0);
                debug_assert_eq!(old_l1, l1);
            }
            // self.watches(cid, "after strengthen_by_elimination case:3-3");
            */
        }
        if self.certification_store.is_active() {
            let ClauseDB {
                ref mut certification_store,
                clause,
                ..
            } = self;
            certification_store.add_clause(&clause[ci].lits);
            certification_store.delete_clause(&new_lits);
        }
        RefClause::Clause(ci)
    }
    // Not in use so far
    fn transform_by_replacement(&mut self, ci: ClauseIndex, new_lits: &mut Vec<Lit>) -> RefClause {
        debug_assert!(1 < new_lits.len());
        //
        //## Clause transform rules
        //
        // There are three cases:
        // 1. a normal clause is merged to a registered bi-clause. [Case:0]
        // 2. a normal clause becomes a new bi-clause.             [Case:2]
        // 3. a normal clause becomes a shorter normal clause.     [Case:3]
        //
        // debug_assert!(new_lits.len() < c.len());
        if new_lits.len() == 2 {
            if let Some(&did) = self.binary_link.search(new_lits[0], new_lits[1]) {
                //
                //## Case:0
                //
                if self.certification_store.is_active() {
                    self.certification_store.delete_clause(new_lits);
                }
                return RefClause::RegisteredClause(did);
            }
            //
            //## Case:2
            //
            // let old_l0 = self[ci].lit0();
            // let old_l1 = self[ci].lit0();
            std::mem::swap(&mut self[ci].lits, new_lits);
            let l0 = self[ci].lit0();
            let l1 = self[ci].lit0();
            // watch_cache[!old_l0].remove_watch(&ci);
            // watch_cache[!old_l1].remove_watch(&ci);
            self.remove_watcher(ci);
            self.binary_link.add(l0, l1, ci);
            self[ci].turn_off(FlagClause::LEARNT);
            self.num_bi_clause += 1;
            let ClauseDB {
                ref clause,
                ref mut certification_store,
                ..
            } = self;

            if certification_store.is_active() {
                certification_store.add_clause(&clause[ci].lits);
                certification_store.delete_clause(new_lits);
            }
        } else {
            //
            //## Case:3
            //
            // let old_l0 = self[ci].lit0();
            // let old_l1 = self[ci].lit0();
            std::mem::swap(&mut self[ci].lits, new_lits);
            let l0 = self[ci].lit0();
            let l1 = self[ci].lit0();

            self.remove_watcher(ci);
            self.insert_watcher(ci, false, !l0);
            self.insert_watcher(ci, true, !l1);

            // maintain_watch_literal \\ assert!(watch_cache[!c.lits[0]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[1]));
            // maintain_watch_literal \\ assert!(watch_cache[!c.lits[1]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[0]));

            if self.certification_store.is_active() {
                self.certification_store.add_clause(new_lits);
                self.certification_store
                    .delete_clause(&self[ci].lits.clone());
            }
        }
        RefClause::Clause(ci)
    }
    // only used in `propagate_at_root_level`
    fn transform_by_simplification(
        &mut self,
        asg: &mut impl AssignIF,
        ci: ClauseIndex,
        deads: &mut HashSet<Lit>,
    ) -> RefClause {
        //
        //## Clause transform rules
        //
        // There are six cases:
        // 1. a binary or normal clause becomes an empty clause.   [Case:0]
        // 2. a binary or normal clause becomes a unit clause.     [Case:1]
        // 3. a normal or binary clause remains as is.             [Case:2]
        // 4. a normal clause is merged to a registered bi-clause. [Case:3-0]
        // 5. a normal clause becomes a new bi-clause.             [Case:3-2]
        // 5. a normal clause becomes a shorter normal clause.     [Case:3-3]
        //
        debug_assert!(!self[ci].is_dead());
        // firstly sweep without consuming extra memory
        let mut need_to_shrink = false;
        for l in self[ci].iter() {
            debug_assert!(!asg.var(l.vi()).is(FlagVar::ELIMINATED));
            match asg.assigned(*l) {
                Some(true) => {
                    self.nullify_clause(ci, deads);
                    return RefClause::Dead;
                }
                Some(false) => {
                    need_to_shrink = true;
                }
                None if asg.var(l.vi()).is(FlagVar::ELIMINATED) => {
                    need_to_shrink = true;
                }
                None => (),
            }
        }
        if !need_to_shrink {
            //
            //## Case:2
            //
            return RefClause::Clause(ci);
        }
        let mut new_lits = self[ci]
            .lits
            .iter()
            .filter(|l| asg.assigned(**l).is_none() && !asg.var(l.vi()).is(FlagVar::ELIMINATED))
            .copied()
            .collect::<Vec<_>>();
        match new_lits.len() {
            0 => RefClause::EmptyClause,             //## Case:0
            1 => RefClause::UnitClause(new_lits[0]), //## Case:1
            2 => {
                //## Case:2
                let l0 = new_lits[0];
                let l1 = new_lits[1];
                debug_assert!(2 < self[ci].lits.len());
                if let Some(&bid) = self.binary_link.search(l0, l1) {
                    //
                    //## Case:3-0
                    //
                    self.nullify_clause(ci, deads);
                    return RefClause::RegisteredClause(bid);
                }
                //
                //## Case:3-2
                //
                // let new_l0 = self[ci].lits[0];
                // let new_l1 = self[ci].lits[1];
                // watch_cache[!c.lits[0]].remove_watch(&ci);
                // watch_cache[!c.lits[1]].remove_watch(&ci);
                self.remove_watcher(ci);
                self.binary_link.add(l0, l1, ci);
                std::mem::swap(&mut self[ci].lits, &mut new_lits);
                self.num_bi_clause += 1;
                if self[ci].is(FlagClause::LEARNT) {
                    self.num_learnt -= 1;
                    self[ci].turn_off(FlagClause::LEARNT);
                }
                let ClauseDB {
                    ref clause,
                    ref mut certification_store,
                    ..
                } = self;
                if certification_store.is_active() {
                    certification_store.add_clause(&clause[ci].lits);
                    certification_store.delete_clause(&new_lits);
                }
                RefClause::Clause(ci)
            }
            _ => {
                //
                //## Case:3-3
                //
                // let old_l0 = self[ci].lit0();
                // let old_l1 = self[ci].lit1();
                std::mem::swap(&mut self[ci].lits, &mut new_lits);
                let l0 = self[ci].lit0();
                let l1 = self[ci].lit1();

                self.remove_watcher(ci);
                self.insert_watcher(ci, false, !l0);
                self.insert_watcher(ci, true, !l1);

                // maintain_watch_literal \\ assert!(watch_cache[!c.lits[0]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[1]));
                // maintain_watch_literal \\ assert!(watch_cache[!c.lits[1]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[0]));

                if self.certification_store.is_active() {
                    let ClauseDB {
                        ref clause,
                        ref mut certification_store,
                        ..
                    } = self;
                    certification_store.add_clause(&clause[ci].lits);
                    certification_store.delete_clause(&new_lits);
                }
                RefClause::Clause(ci)
            }
        }
    }
    // used in `propagate`, `propagate_sandbox`, and `handle_conflict` for chronoBT
    #[inline]
    fn transform_by_updating_watch(
        &mut self,
        prev: ClauseIndex,
        ci: ClauseIndex,
        old: usize,
        new: usize,
    ) -> ClauseIndex {
        //
        //## Clause transform rules
        //
        // There is one case under non maintain_blocker:
        // 1. one deletion (if not removed), and one insertion of watch caches
        //
        // There is one case under maintain_blocker:
        // 1. one deletion (if not removed), one insertion, and one update
        //
        // So the proceduce is
        // 1. delete an old one                   [Step:1]
        // 2. insert a new watch                  [Step:2]
        // 3. update a blocker cach e             [Step:3]

        debug_assert!(!self[ci].is_dead());
        debug_assert!(old < 2);
        debug_assert!(1 < new);
        debug_assert!(!self[ci].is(FlagClause::SWEEPED));
        //## Step:1
        let ret = if old == 0 {
            self[ci].link0
        } else {
            self[ci].link1
        };
        let second = self.remove_next_watcher(prev, !self[ci].lits[old]);
        // watch_cache[!c.lits[old]].remove_watch(&ci);

        //## Step:2
        // assert!(watch_cache[!c.lits[new]].iter().all(|e| e.0 != cid));
        self[ci].lits.swap(old, new);
        // so old becomes new now
        self.insert_watcher(ci, second, !self[ci].lits[old]);
        let c = &mut self[ci];
        c.search_from = ((new + 1) % (c.len() - 2)) as u16;
        ret
        // self[ci].search_from = ((new + 1) % (self[ci].len() - 2)) as u16;
        // watch_cache[!c.lits[new]].insert_watch(ci, c.lits[other]);
        // maintain_watch_literal
        // assert!(watch_cache[!c.lits[0]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[1]));
        // maintain_watch_literal
        // assert!(watch_cache[!c.lits[1]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[0]));
    }
    fn update_at_analysis(&mut self, asg: &impl AssignIF, ci: ClauseIndex) -> bool {
        let c = &mut self.clause[ci];
        // Updating LBD at every analysis seems redundant.
        // But it's crucial. Don't remove the below.
        let rank = c.update_lbd(asg);
        let learnt = c.is(FlagClause::LEARNT);
        if learnt {
            #[cfg(feature = "just_used")]
            c.turn_on(FlagClause::USED);
            #[cfg(feature = "clause_rewading")]
            self.reward_at_analysis(ci);
        }
        if 1 < rank {
            self.lb_entanglement.update(rank as f64);
        }
        learnt
    }
    /// reduce the number of 'learnt' or *removable* clauses.
    fn reduce(&mut self, asg: &mut impl AssignIF, setting: ReductionType) {
        impl Clause {
            fn reverse_activity_sum(&self, asg: &impl AssignIF) -> f64 {
                self.iter().map(|l| 1.0 - asg.activity(l.vi())).sum()
            }
            fn lbd(&self) -> f64 {
                self.rank as f64
            }
        }
        let mut using: HashSet<ClauseIndex> = HashSet::new();
        if asg.decision_level() != asg.root_level() {
            for v in asg.var_iter_mut() {
                if let AssignReason::Implication(ci) = v.reason {
                    using.insert(ci);
                }
            }
        }
        let ClauseDB {
            ref mut clause,
            ref mut num_reduction,

            #[cfg(feature = "clause_rewarding")]
            ref tick,
            #[cfg(feature = "clause_rewarding")]
            ref activity_decay,
            ..
        } = self;
        *num_reduction += 1;

        let mut perm: Vec<OrderedProxy<ClauseIndex>> = Vec::with_capacity(clause.len());
        let mut alives = 0;
        for (ci, c) in clause
            .iter_mut()
            .enumerate()
            .skip(1)
            .filter(|(_, c)| !c.is_dead())
        {
            c.update_lbd(asg);

            #[cfg(feature = "clause_rewarding")]
            c.update_activity(*tick, *activity_decay, 0.0);

            if !c.is(FlagClause::LEARNT) || using.contains(&ci) {
                continue;
            }
            // There's no clause stored in `reason` because the decision level is 'zero.'
            debug_assert_ne!(
                asg.reason(c.lit0().vi()),
                AssignReason::Implication(ci),
                "Lit {} {:?} level {}, dl: {}",
                i32::from(c.lit0()),
                asg.assigned(c.lit0()),
                asg.level(c.lit0().vi()),
                asg.decision_level(),
            );
            alives += 1;
            match setting {
                ReductionType::RASonADD(_) => {
                    perm.push(OrderedProxy::new(ci, c.reverse_activity_sum(asg)));
                }
                ReductionType::RASonALL(cutoff, _) => {
                    let value = c.reverse_activity_sum(asg);
                    if cutoff < value.min(c.rank_old as f64) {
                        perm.push(OrderedProxy::new(ci, value));
                    }
                }
                ReductionType::LBDonADD(_) => {
                    perm.push(OrderedProxy::new(ci, c.lbd()));
                }
                ReductionType::LBDonALL(cutoff, _) => {
                    let value = c.rank.min(c.rank_old);
                    if cutoff < value {
                        perm.push(OrderedProxy::new(ci, value as f64));
                    }
                }
            }
        }
        let keep = match setting {
            ReductionType::RASonADD(size) => perm.len().saturating_sub(size),
            ReductionType::RASonALL(_, scale) => (perm.len() as f64).powf(1.0 - scale) as usize,
            ReductionType::LBDonADD(size) => perm.len().saturating_sub(size),
            ReductionType::LBDonALL(_, scale) => (perm.len() as f64).powf(1.0 - scale) as usize,
        };
        self.reduction_threshold = match setting {
            ReductionType::RASonADD(_) | ReductionType::RASonALL(_, _) => {
                keep as f64 / alives as f64
            }
            ReductionType::LBDonADD(_) | ReductionType::LBDonALL(_, _) => {
                -(keep as f64) / alives as f64
            }
        };
        perm.sort();
        let mut deads: HashSet<Lit> = HashSet::new();
        for i in perm.iter().skip(keep) {
            self.nullify_clause(i.to(), &mut deads);
        }
        self.collect_dead_watchers(&mut deads);
    }
    fn reset(&mut self) {
        let mut deads: HashSet<Lit> = HashSet::new();
        for ci in 1..self.len() {
            let c = &self.clause[ci];
            if c.is(FlagClause::LEARNT) && (self.co_lbd_bound as usize) < c.len() {
                self.nullify_clause(ci, &mut deads);
            }
        }
        self.collect_dead_watchers(&mut deads);
    }
    fn certificate_add_assertion(&mut self, lit: Lit) {
        self.certification_store.add_clause(&[lit]);
    }
    fn certificate_save(&mut self) {
        self.certification_store.close();
    }
    fn check_size(&self) -> Result<bool, SolverError> {
        if self.soft_limit == 0 || self.num_clause <= self.soft_limit {
            let nc = self.derefer(property::Tusize::NumClause);
            Ok(0 == self.soft_limit || 4 * nc < 3 * self.soft_limit)
        } else {
            Err(SolverError::OutOfMemory)
        }
    }
    fn validate(&self, model: &[Option<bool>], strict: bool) -> Option<ClauseIndex> {
        for (i, c) in self.clause.iter().enumerate().skip(1) {
            if c.is_dead() || (strict && c.is(FlagClause::LEARNT)) {
                continue;
            }
            match c.evaluate(model) {
                Some(false) => return Some(i),
                None if strict => return Some(i),
                _ => (),
            }
        }
        None
    }
    #[allow(clippy::unnecessary_cast)]
    fn minimize_with_bi_clauses(&mut self, asg: &impl AssignIF, vec: &mut Vec<Lit>) {
        if vec.len() <= 1 {
            return;
        }
        self.lbd_temp[0] += 1;
        let key = self.lbd_temp[0];
        for l in &vec[1..] {
            self.lbd_temp[l.vi() as usize] = key;
        }
        let l0 = vec[0];
        let mut num_sat = 0;
        for (_, ci) in self.binary_link.connect_with(l0).iter() {
            let c = &self.clause[*ci];
            debug_assert!(c[0] == l0 || c[1] == l0);
            let other = c[(c[0] == l0) as usize];
            let vi = other.vi();
            if self.lbd_temp[vi] == key && asg.assigned(other) == Some(true) {
                num_sat += 1;
                self.lbd_temp[vi] = key - 1;
            }
        }
        if 0 < num_sat {
            self.lbd_temp[l0.vi()] = key;
            vec.retain(|l| self.lbd_temp[l.vi()] == key);
        }
    }
    fn complete_bi_clauses(&mut self, asg: &mut impl AssignIF) {
        while let Some(lit) = self.bi_clause_completion_queue.pop() {
            self.complete_bi_clauses_with(asg, lit);
        }
    }
    fn preppend_clauses(&mut self, force: bool) {
        self.preppend_head = force;
    }

    #[cfg(feature = "incremental_solver")]
    fn make_permanent_immortal(&mut self, cid: ClauseId) {
        self.eliminated_permanent.push(
            self.clause[NonZeroU32::get(cid.ordinal) as usize]
                .lits
                .clone(),
        );
    }
    #[cfg(feature = "boundary_check")]
    fn watch_cache_contains(&self, lit: Lit, cid: ClauseId) -> bool {
        self.watch_cache[lit].iter().any(|w| w.0 == cid)
    }
    #[cfg(feature = "boundary_check")]
    fn watch_caches(&self, cid: ClauseId, mes: &str) -> (Vec<Lit>, Vec<Lit>) {
        // let mut _found = None;
        debug_assert!(!cid.is_lifted_lit());
        let c = &self[cid];
        debug_assert!(1 < c.len());
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        if 2 == c.lits.len() {
            assert!(
                self.binary_link.search(l0, l1).is_some(),
                "(watch_cache health check: binary clause l0 not found){}, cid{}{:?}",
                mes,
                cid,
                c
            );
            assert!(
                self.binary_link.search(l1, l0).is_some(),
                "(watch_cache health check: binary clause l1 not found){}, cid{}{:?}",
                mes,
                cid,
                c
            );
            assert!(
                !self.watch_cache[!l0].iter().any(|wc| wc.0 == cid),
                "(watch_cache health check: binary clause l0 found in watch_cache){}, cid{}{:?}",
                mes,
                cid,
                c
            );
            assert!(
                !self.watch_cache[!l1].iter().any(|wc| wc.0 == cid),
                "(watch_cache health check: binary clause l1 found in watch cache){}, cid{}{:?}",
                mes,
                cid,
                c
            );
            (vec![l1], vec![l0])
        } else {
            assert!(
                self.watch_cache[!l0].iter().any(|wc| wc.0 == cid),
                "(watch_cache health check: clause l0 not found){}, cid{}{:?}",
                mes,
                cid,
                c
            );
            assert!(
                self.watch_cache[!l1].iter().any(|wc| wc.0 == cid),
                "(watch_cache health check: clause l1 not found){}, cid{}{:?}",
                mes,
                cid,
                c
            );
            (
                self.watch_cache[!l0]
                    .iter()
                    .filter(|w| w.0 == cid)
                    .map(|w| w.1)
                    .collect(),
                self.watch_cache[!l1]
                    .iter()
                    .filter(|w| w.0 == cid)
                    .map(|w| w.1)
                    .collect(),
            )
        }
    }
    #[cfg(feature = "boundary_check")]
    fn is_garbage_collected(&mut self, cid: ClauseId) -> Option<bool> {
        self[cid].is_dead().then(|| self.freelist.contains(&cid))
    }
    #[cfg(not(feature = "no_IO"))]
    /// dump all active clauses and assertions as a CNF file.
    fn dump_cnf(&self, asg: &impl AssignIF, fname: &Path) {
        use std::fs::File;

        let nv = asg.derefer(crate::assign::property::Tusize::NumVar);
        for vi in 1..nv {
            if asg.var(vi).is(FlagVar::ELIMINATED) && asg.assign(vi).is_some() {
                panic!("conflicting var {} {:?}", vi, asg.assign(vi));
            }
        }
        let Ok(out) = File::create(fname) else {
            return;
        };
        let mut buf = std::io::BufWriter::new(out);
        let na = asg.derefer(crate::assign::property::Tusize::NumAssertedVar);
        let nc = self.iter().skip(1).filter(|c| !c.is_dead()).count();
        buf.write_all(format!("p cnf {} {}\n", nv, nc + na).as_bytes())
            .unwrap();
        for c in self.iter().skip(1) {
            if c.is_dead() {
                continue;
            }
            for l in c.iter() {
                buf.write_all(format!("{} ", i32::from(*l)).as_bytes())
                    .unwrap();
            }
            buf.write_all(b"0\n").unwrap();
        }
        buf.write_all(b"c from trail\n").unwrap();
        for x in asg.stack_iter().take(asg.len_upto(0)) {
            buf.write_all(format!("{} 0\n", i32::from(*x)).as_bytes())
                .unwrap();
        }
    }
}

impl ClauseDB {
    /// formula: -a => b and b => c implies -a => c
    /// clause: [a, b] and [-b, c] deduces [a, c]
    /// map: [a].get(b), [!b].get(c), [a].get(c)
    /// rename: [lit].get(other), [!other].get(third), [a].get(third)
    fn complete_bi_clauses_with(&mut self, asg: &mut impl AssignIF, lit: Lit) {
        let mut vec: Vec<Vec<Lit>> = Vec::new();
        // [lit, other]
        for (other, _) in self.binary_link.connect_with(lit) {
            // [!other, third]
            for (third, _) in self.binary_link.connect_with(!*other) {
                if lit.vi() != third.vi() && self.binary_link.search(lit, *third).is_none() {
                    // the new [lit, third] should be added.
                    vec.push(vec![lit, *third]);
                }
            }
        }
        for pair in vec.iter_mut() {
            self.new_clause(asg, pair, false);
            self.num_bi_clause_completion += 1;
        }
    }
    /// return `true` if a literal pair `(l0, l1)` is registered.
    ///```ignore
    /// use splr::types::*;
    /// use crate::splr::cdb::ClauseDBIF;
    ///
    /// let config = Config::default();
    /// let cnf = CNFDescription {
    ///     num_of_variables: 4,
    ///     ..CNFDescription::default()
    /// };
    /// let mut asg = splr::assign::AssignStack::instantiate(&config, &cnf);
    /// let mut cdb = splr::cdb::ClauseDB::instantiate(&config, &cnf);
    /// let l1 = splr::types::Lit::from(1);
    /// let l2 = splr::types::Lit::from(2);
    /// let l3 = splr::types::Lit::from(3);
    /// cdb.new_clause(&mut asg, &mut vec![l1, l2], false);
    /// cdb.new_clause(&mut asg, &mut vec![!l1, !l2, !l3], false);
    /// assert!(cdb.link_to_cid(l1, l2).is_some());
    /// assert!(cdb.link_to_cid(!l1, l2).is_none());
    /// assert!(cdb.link_to_cid(l1, !l2).is_none());
    /// assert!(cdb.link_to_cid(!l1, !l2).is_none());
    ///```
    ///
    /// this is equivalent to the following:
    ///```ignore
    /// bi_clause[l0].get(&l1).is_some()
    ///```
    fn link_to_cid(&self, l0: Lit, l1: Lit) -> Option<&ClauseIndex> {
        self.binary_link.search(l0, l1)
    }
}

impl Clause {
    /// evaluate a clause and return Option<bool>.
    /// - `Some(true)` -- the literals is satisfied by a literal
    /// - `Some(false)` -- the literals is unsatisfied; no unassigned literal
    /// - `None` -- the literals contains an unassigned literal
    fn evaluate(&self, model: &[Option<bool>]) -> Option<bool> {
        let mut falsified = Some(false);
        for l in self.lits.iter() {
            match model[l.vi()] {
                Some(x) if x == bool::from(*l) => return Some(true),
                Some(_) => (),
                None => falsified = None,
            }
        }
        falsified
    }
}

impl ClauseWeaverIF for ClauseDB {
    fn get_watcher_link(&mut self, lit: Lit) -> ClauseIndex {
        self.watch[ClauseIndex::from(lit)]
    }
    fn get_free_index(&mut self) -> ClauseIndex {
        let ci = self.watch[Self::FREE_INDEX];
        if ci == Self::HEAD_INDEX {
            self.clause.push(Clause::default());
            self.clause.len() - 1
        } else {
            let next = self.clause[ci].next_free();
            self.watch[Self::FREE_INDEX] = next;
            ci
        }
    }
    fn insert_watcher(&mut self, ci: ClauseIndex, second: bool, lit: Lit) {
        debug_assert!(
            self[ci].lits[0] == !lit || self[ci].lits[1] == !lit,
            "invalid lit layout {:?}, lit: {:?}",
            self[ci],
            lit
        );
        let head = self.watch[usize::from(lit)];
        self.watch[usize::from(lit)] = ci;
        debug_assert_ne!(ci, head);
        if second {
            self.clause[ci].link1 = head;
        } else {
            self.clause[ci].link0 = head;
        }
    }
    /// O(1) implementation
    fn remove_next_watcher(&mut self, ci: ClauseIndex, lit: Lit) -> bool {
        if ci == Self::HEAD_INDEX {
            let next1 = self.watch[usize::from(lit)];
            let next2 = self.clause[next1].next_for_lit(lit);
            self.watch[usize::from(lit)] = next2;
            debug_assert!(self[next1].lits[0] == !lit || self[next1].lits[1] == !lit);
            debug_assert!(
                next2 == Self::HEAD_INDEX
                    || self[next2].lits[0] == !lit
                    || self[next2].lits[1] == !lit
            );
            self[next1].lits[1] == !lit
        } else {
            let next1 = self.clause[ci].next_for_lit(lit);
            let next2 = self.clause[next1].next_for_lit(lit);
            *self.clause[ci].next_for_lit_mut(lit) = next2;
            debug_assert!(self[ci].lits[1] == !lit || self[ci].lits[0] == !lit);
            debug_assert!(self[next1].lits[0] == !lit || self[next1].lits[1] == !lit);
            debug_assert!(
                next2 == Self::HEAD_INDEX
                    || self[next2].lits[0] == !lit
                    || self[next2].lits[1] == !lit
            );
            self[next1].lits[1] == !lit
        }
    }
    /// O(N) implementation
    fn remove_watcher(&mut self, ci: ClauseIndex) {
        let lit0 = !self[ci].lit0();
        let lit1 = !self[ci].lit1();
        let mut index = self.watch[usize::from(lit0)];
        let mut prev = Self::HEAD_INDEX;
        while index != Self::HEAD_INDEX {
            if index == ci {
                self.remove_next_watcher(prev, lit0);
                break;
            }
            prev = index;
            index = self[index].next_for_lit(lit0);
        }
        // assert_ne!(index, HEAD_INDEX);
        let mut index = self.watch[usize::from(lit1)];
        let mut prev = Self::HEAD_INDEX;
        while index != Self::HEAD_INDEX {
            if index == ci {
                self.remove_next_watcher(prev, lit1);
                break;
            }
            prev = index;
            index = self[index].next_for_lit(lit1);
        }
        // assert_ne!(index, HEAD_INDEX);
    }
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<ClauseIndex> {
        // ci 0 must refer to the header
        let nc = clauses.len();
        for (i, c) in clauses.iter_mut().enumerate().skip(1) {
            *c.next_free_mut() = (i + 1) % nc;
            c.turn_on(FlagClause::DEAD);
        }
        let mut watches = vec![ClauseIndex::default(); 2 * (num_vars + 1)];
        *clauses[nc - 1].next_free_mut() = Self::HEAD_INDEX;
        watches[Self::FREE_INDEX] = if 1 < nc { 1 } else { 0 };
        watches
    }
    /// This and the sandbox version are the only functions that make clause DEAD.
    fn nullify_clause(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>) {
        debug_assert!(!self[ci].is_dead());
        debug_assert!(!self[ci].is(FlagClause::SWEEPED));
        let c = &mut self.clause[ci];
        self.certification_store.delete_clause(&c.lits);
        let l0 = c.lit0();
        let l1 = c.lit1();
        self.num_clause -= 1;
        if c.is(FlagClause::LEARNT) {
            self.num_learnt -= 1;
        }
        c.turn_on(FlagClause::DEAD);
        if c.lits.len() == 2 {
            self.binary_link
                .remove(l0, l1)
                .expect("Error (remove_clause)");
            self.num_bi_clause -= 1;
            self[ci].turn_on(FlagClause::SWEEPED);
            self.move_to_free_list(ci);
        } else {
            deads.insert(!l0);
            deads.insert(!l1);
        }
    }
    fn nullify_clause_sandbox(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>) {
        debug_assert!(!self[ci].is_dead());
        let c = &mut self.clause[ci];
        let l0 = c.lit0();
        let l1 = c.lit1();
        c.turn_on(FlagClause::DEAD);
        if c.lits.len() == 2 {
            self.binary_link
                .remove(l0, l1)
                .expect("Error (remove_clause)");
            self.move_to_free_list(ci);
        } else {
            deads.insert(!l0);
            deads.insert(!l1);
        }
    }
    fn collect_dead_watchers(&mut self, targets: &mut HashSet<Lit>) {
        for lit in targets.iter() {
            let mut prev: ClauseIndex = Self::HEAD_INDEX;
            let mut ci: ClauseIndex = self.watch[usize::from(*lit)];
            while ci != Self::HEAD_INDEX {
                if self[ci].is_dead() {
                    let next_ci = self[ci].next_for_lit(*lit);
                    self.remove_next_watcher(prev, *lit);
                    if self[ci].is(FlagClause::SWEEPED) {
                        self.move_to_free_list(ci);
                        // self[ci].turn_off(FlagClause::SWEEPED);
                        if let Err(s) = self.check_dead_watcher_status(ci) {
                            panic!("{s}");
                        }
                    } else {
                        self[ci].turn_on(FlagClause::SWEEPED);
                    }
                    ci = next_ci;
                    continue;
                }
                prev = ci;
                ci = self[ci].next_for_lit(*lit);
            }
        }
        targets.clear();
    }
    fn check_all_watchers_status(&self) -> Result<(), String> {
        let mut free: HashSet<ClauseIndex> = HashSet::new();
        let mut ci = self.watch[Self::FREE_INDEX];
        while ci != Self::HEAD_INDEX {
            free.insert(ci);
            ci = self.clause[ci].next_free();
        }
        // for ci in 1..self.len() {
        //     if self[ci].is_dead() {
        //         self.check_dead_watcher_status(ci)?;
        //     } else {
        //         self.check_watcher_status(ci, self[ci].is_dead())?;
        //     }
        // }
        Ok(())
    }
    fn check_watcher_status(&self, ci: ClauseIndex, should_be_dead: bool) -> Result<(), String> {
        assert!(should_be_dead || !self[ci].is_dead());
        let len = self.len();
        let l0 = self[ci].lit0();
        let l1 = self[ci].lit1();
        let mut count = 0;
        let mut found = false;
        if self[ci].lits.len() == 2 {
            let mut i = self.watch[usize::from(!l0)];
            while i != Self::HEAD_INDEX {
                if i == ci {
                    found = true;
                }
                i = self[i].next_for_lit(!l0);
                count += 1;
                if len < count {
                    return Err(format!(
                        "watcher list.{} for {}:{} became a loop",
                        !l0, ci, &self[ci]
                    ));
                }
            }
            if found {
                return Err(format!(
                    "\nWatcher binary clause {}:{:?} is included in watcher list:{}",
                    ci, &self[ci], !l0
                ));
            }
            let mut i = self.watch[usize::from(!l1)];
            count = 0;
            found = false;
            while i != Self::HEAD_INDEX {
                if i == ci {
                    found = true;
                }
                i = self[i].next_for_lit(!l1);
                count += 1;
                if len < count {
                    return Err(format!(
                        "watcher list {}:for {}:{} became a loop",
                        !l0, ci, &self[ci]
                    ));
                }
            }
            if found {
                return Err(format!(
                    "\nWatcher binary clause {}:{:?} is included in watcher list:{}",
                    ci, &self[ci], !l1
                ));
            }
        } else {
            let mut i = self.watch[usize::from(!l0)];
            found = false;
            while i != Self::HEAD_INDEX {
                if i == ci {
                    found = true;
                }
                i = self[i].next_for_lit(!l0);
                count += 1;
                if len < count {
                    return Err(format!(
                        "watcher list:{} for {}:{} became a loop",
                        !l0, ci, &self[ci]
                    ));
                }
            }
            if !found {
                return Err(format!(
                    "\nWatcher link {} does not include {}:{:?}",
                    !l0, ci, &self[ci]
                ));
            }
            let mut i = self.watch[usize::from(!l1)];
            found = false;
            while i != Self::HEAD_INDEX {
                if i == ci {
                    found = true;
                }
                i = self[i].next_for_lit(!l1);
                count += 1;
                if len < count {
                    return Err(format!(
                        "watcher list {} for {}:{} became a loop",
                        !l1, ci, &self[ci]
                    ));
                }
            }
            if !found {
                return Err(format!(
                    "\nWatcher link {} does not include {}:{:?}",
                    !l1, ci, &self[ci]
                ));
            }
        }
        Ok(())
    }
    fn check_dead_watcher_status(&self, ci: ClauseIndex) -> Result<(), String> {
        assert!(self[ci].is_dead());
        let len = self.len();
        let l0 = self[ci].lit0();
        let l1 = self[ci].lit1();
        let mut count = 0;
        let mut found = false;
        if self[ci].is(FlagClause::SWEEPED) {
            let mut i = self.watch[Self::FREE_INDEX];
            while i != Self::HEAD_INDEX {
                if i == ci {
                    found = true;
                }
                i = self[i].next_free();
                count += 1;
                if len < count {
                    return Err(format!("Free list for {}:{} became a loop", ci, &self[ci]));
                }
            }
            if !found {
                return Err(format!(
                    "\nDead clause {}:{:?} is not included in the free list",
                    ci, &self[ci]
                ));
            }
            return Ok(());
        }
        if self[ci].lits.len() == 2 {
            let mut i = self.watch[usize::from(!l0)];
            while i != Self::HEAD_INDEX {
                if i == ci {
                    found = true;
                }
                i = self[i].next_for_lit(!l0);
                count += 1;
                if len < count {
                    return Err(format!(
                        "watcher list.{} for {}:{} became a loop",
                        !l0, ci, &self[ci]
                    ));
                }
            }
            if found {
                return Err(format!(
                    "\nDead binary clause {}:{:?} is included in watcher list:{}",
                    ci, &self[ci], !l0
                ));
            }
            let mut i = self.watch[usize::from(!l1)];
            count = 0;
            found = false;
            while i != Self::HEAD_INDEX {
                if i == ci {
                    found = true;
                }
                i = self[i].next_for_lit(!l1);
                count += 1;
                if len < count {
                    return Err(format!(
                        "\nwatcher list {}:for {}:{} became a loop",
                        !l0, ci, &self[ci]
                    ));
                }
            }
            if found {
                return Err(format!(
                    "\nDead binary clause {}:{:?} is included in watcher list:{}",
                    ci, &self[ci], !l1
                ));
            }
        } else {
            let mut i = self.watch[usize::from(!l0)];
            found = false;
            while i != Self::HEAD_INDEX {
                if i == ci {
                    found = true;
                }
                i = self[i].next_for_lit(!l0);
                count += 1;
                if len < count {
                    return Err(format!(
                        "\nwatcher list:{} for {}:{} became a loop",
                        !l0, ci, &self[ci]
                    ));
                }
            }
            if found {
                return Err(format!(
                    "\nWatcher link {} includes {}:{:?}",
                    !l0, ci, &self[ci]
                ));
            }
            let mut i = self.watch[usize::from(!l1)];
            found = false;
            while i != Self::HEAD_INDEX {
                if i == ci {
                    found = true;
                }
                i = self[i].next_for_lit(!l1);
                count += 1;
                if len < count {
                    return Err(format!(
                        "watcher list {} for {}:{} became a loop",
                        !l1, ci, &self[ci]
                    ));
                }
            }
            if found {
                return Err(format!(
                    "\nDead link {} includes {}:{:?}",
                    !l1, ci, &self[ci]
                ));
            }
        }
        Ok(())
    }
    fn check_chain_connectivity(&self, allow_dead: bool) -> Result<(), String> {
        // check whether all watcher lists are loops.
        let len = self.len();
        for (l, h) in self.watch.iter().enumerate().skip(2) {
            let mut ci = *h;
            let mut count = 0;
            while ci != Self::HEAD_INDEX {
                if !allow_dead && self[ci].is_dead() {
                    return Err(format!(
                        "watcher list {} contains a dead clause {}:{:?}",
                        l, ci, self[ci]
                    ));
                }
                ci = self[ci].next_for_lit(Lit::from(l));
                count += 1;
                if len < count {
                    return Err(format!(
                        "watcher list {} for {}:{} became a loop",
                        l, ci, &self[ci]
                    ));
                }
            }
        }
        Ok(())
    }
}

impl ClauseDB {
    fn move_to_free_list(&mut self, ci: ClauseIndex) {
        // Note: free list is a single-linked list
        assert!(self[ci].is_dead());
        let first = self.watch[Self::FREE_INDEX];
        self.watch[Self::FREE_INDEX] = ci;
        *self.clause[ci].next_free_mut() = first;
    }
}

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
    use super::*;
    use crate::assign::{AssignStack, PropagateIF, VarManipulateIF};

    fn lit(i: i32) -> Lit {
        Lit::from(i)
    }

    #[test]
    fn test_clause_instantiation() {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asg = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        // Now `asg.level` = [_, 1, 2, 3, 4, 5, 6].
        // let c0 = cdb
        //     .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3), lit(4)], false)
        //     .as_ci();

        asg.assign_by_decision(lit(-2)); // at level 1
        asg.assign_by_decision(lit(1)); // at level 2
                                        // Now `asg.level` = [_, 2, 1, 3, 4, 5, 6].
        assert_eq!(asg.level(1), 2);
        let c1 = cdb
            .new_clause(&mut asg, &mut vec![lit(1), lit(2), lit(3)], false)
            .as_ci();
        let c = &cdb[c1];

        assert!(!c.is_dead());
        assert!(!c.is(FlagClause::LEARNT));
        #[cfg(feature = "just_used")]
        assert!(!c.is(Flag::USED));
        let c2 = cdb
            .new_clause(&mut asg, &mut vec![lit(-1), lit(2), lit(3)], true)
            .as_ci();
        let c = &cdb[c2];
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
            .as_ci();
        let c2 = cdb
            .new_clause(&mut asg, &mut vec![lit(-1), lit(4)], false)
            .as_ci();
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
            .as_ci();
        assert_eq!(cdb.len(), 2);
        assert_eq!(cdb[c1][0..].iter().map(|l| i32::from(*l)).sum::<i32>(), 6);
        let mut iter = cdb[c1][0..].iter();
        assert_eq!(iter.next(), Some(&lit(1)));
        assert_eq!(iter.next(), Some(&lit(2)));
        assert_eq!(iter.next(), Some(&lit(3)));
        assert_eq!(iter.next(), None);
    }
}

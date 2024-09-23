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
    binary::BinaryLinkDB, ci::LiftedClauseIF, clause::*, db::ClauseDB, property::*,
    sls::StochasticLocalSearchIF, unsat_certificate::CertificationStore, vivify::VivifyIF,
    weaver::*,
};

use {
    self::binary::BinaryLinkIF,
    crate::{assign::AssignIF, types::*},
    ema::ProgressLBD,
    std::{
        ops::IndexMut,
        slice::{Iter, IterMut},
    },
};

#[cfg(not(feature = "no_IO"))]
use std::{io::Write, path::Path};

/// API for clause management like [`reduce`](`crate::cdb::ClauseDBIF::reduce`), [`new_clause`](`crate::cdb::ClauseDBIF::new_clause`), [`remove_clause`](`crate::cdb::ClauseDBIF::remove_clause`), and so on.
pub trait ClauseDBIF:
    Instantiate
    + IndexMut<ClauseIndex, Output = Clause>
    + IndexMut<WatchLiteralIndex, Output = Lit>
    + ClauseWeaverIF
    + PropertyDereference<property::Tusize, usize>
    + PropertyDereference<property::Tf64, f64>
    + ActivityIF<ClauseIndex>
{
    #[cfg(feature = "boundary_check")]
    fn check_chains(&self, ci: ClauseIndex);
    /// return the length of `clause`.
    fn len(&self) -> usize;
    /// return true if it's empty.
    fn is_empty(&self) -> bool;
    /// return an iterator.
    fn iter(&self) -> Iter<'_, Clause>;
    /// return a mutable iterator.
    fn iter_mut(&mut self) -> IterMut<'_, Clause>;

    //
    //## clause transformation
    //

    /// swap i-th watch with j-th literal then update watch caches correctly
    fn transform_by_updating_watch(
        &mut self,
        wli: WatchLiteralIndex,
        new: usize,
    ) -> WatchLiteralIndex;
    /// allocate a new clause and return its id.
    /// Note this removes an eliminated Lit `p` from a clause. This is an O(n) function!
    /// This returns `true` if the clause became a unit clause.
    /// And this is called only from `Eliminator::strengthen_clause`.
    fn new_clause(&mut self, asg: &mut impl AssignIF, v: &mut Vec<Lit>, learnt: bool) -> RefClause;
    fn delete_clause(&mut self, ci: ClauseIndex);
    fn transform_by_elimination(&mut self, ci: ClauseIndex, p: Lit) -> RefClause;
    /// generic clause transformer (not in use)
    fn transform_by_replacement(&mut self, ci: ClauseIndex, vec: &mut Vec<Lit>) -> RefClause;
    /// check satisfied and nullified literals in a clause
    fn transform_by_simplification(
        &mut self,
        asg: &mut impl AssignIF,
        ci: ClauseIndex,
    ) -> RefClause;
    /// reduce learnt clauses
    /// # CAVEAT
    /// *precondition*: decision level == 0.
    fn reduce(&mut self, asg: &mut impl AssignIF, threshold: f64);
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
            // lb_entanglement: Ema2::new(1_000).with_slow(80_000).with_value(16.0),
            lb_entanglement: Ema2::new(16).with_slow(8192).with_value(16.0),

            #[cfg(all(feature = "clause_elimination", not(feature = "incremental_solver")))]
            eliminated_permanent: Vec::new(),
        }
    }
}

impl ClauseDBIF for ClauseDB {
    #[cfg(feature = "boundary_check")]
    fn check_chains(&self, ci: ClauseIndex) {
        for (_l, h) in self.watch.iter().enumerate().skip(2) {
            let mut nr: WatchLiteralIndex = h.next;
            while !nr.is_none() {
                assert!(!self[nr.as_ci()].is_dead());
                nr = self[nr.as_ci()].next_watch(nr.as_wi());
            }
        }
        if ci != 0 {
            assert!(!self[ci].lits.is_empty());
            let l0 = !self[ci].lits[0];
            let l1 = !self[ci].lits[1];
            let mut nr = self.watch[usize::from(l0)].next;
            let mut found = false;
            while !nr.is_none() {
                if nr.as_ci() == ci {
                    found = true;
                    break;
                }
                nr = self[nr.as_ci()].next_watch(nr.as_wi());
            }
            assert_eq!(2 < self[ci].lits.len(), found);

            nr = self.watch[usize::from(l1)].next;
            found = false;
            while !nr.is_none() {
                if nr.as_ci() == ci {
                    found = true;
                    break;
                }
                nr = self[nr.as_ci()].next_watch(nr.as_wi());
            }
            assert_eq!(2 < self[ci].lits.len(), found);
        }
    }
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
    fn new_clause(
        &mut self,
        asg: &mut impl AssignIF,
        vec: &mut Vec<Lit>,
        learnt: bool,
    ) -> RefClause {
        debug_assert!(1 < vec.len());
        // debug_assert!(vec.iter().all(|l| !vec.contains(&!*l)), "{vec:?}");
        if vec.len() == 2 {
            if let Some(ci) = self.link_to_cid(vec[0], vec[1]) {
                self.num_reregistration += 1;
                return RefClause::RegisteredClause(ci);
            }
        }
        self.certification_store.add_clause(vec);
        let ci = self.get_free_index();
        debug_assert_ne!(0, ci);
        self.clause[ci].flags = FlagClause::empty();
        std::mem::swap(&mut self[ci].lits, vec);
        self.weave(ci);
        let len2 = self.clause[ci].lits.len() == 2;
        let l0 = self.clause[ci].lits[0];
        let l1 = self.clause[ci].lits[1];
        if len2 {
            self.clause[ci].rank = 1;
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
            let ClauseDB {
                ref mut clause,
                ref mut lbd_temp,
                ..
            } = self;
            clause[ci].update_lbd(asg, lbd_temp);
            debug_assert_eq!(l0, self[ci].lits[0]);
            debug_assert_eq!(l1, self[ci].lits[1]);
        }
        self.clause[ci].search_from = 0;
        self.lbd.update(self[ci].rank);
        self.num_clause += 1;
        if learnt {
            if len2 {
                self.num_bi_learnt += 1;
            } else {
                self.clause[ci].turn_on(FlagClause::LEARNT);
                self.num_learnt += 1;
                if self.clause[ci].rank <= 2 {
                    self.num_lbd2 += 1;
                }
            }
        }

        #[cfg(feature = "clause_rewarding")]
        {
            self.clause[ci].activity = 0.0;
            self.clause[ci].timestamp = self.tick;
        }
        #[cfg(feature = "keep_just_used_clauses")]
        {
            self.clause[ci].turn_on(FlagClause::NEW_CLAUSE);
        }
        // assert_ne!(self.clause[ci].lit0(), self.clause[ci].lit1());
        RefClause::Clause(ci)
    }
    fn delete_clause(&mut self, ci: ClauseIndex) {
        debug_assert_ne!(Lit::default(), self.clause[ci].lit1());
        let len2 = self.clause[ci].len() == 2;
        let c = &self.clause[ci];
        self.certification_store.delete_clause(&c.lits);
        self.num_clause -= 1;
        if c.is(FlagClause::LEARNT) {
            self.num_learnt -= 1;
        }
        if len2 {
            self.num_bi_clause -= 1;
        }
        if len2 {
            self.binary_link
                .remove(self.clause[ci].lits[0], self.clause[ci].lits[1])
                .expect("ilegal biclause found");
        }
        self.unweave(ci, NEFR_WATCH_INDEX);
        self.reweave(ci, FREE_WATCH_INDEX, FREE_WATCH_INDEX);
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
        debug_assert!(1 < usize::from(!p));
        debug_assert!(1 < self[ci].lits.len());
        //
        //## Case:2-0
        //
        if self[ci].lits.len() == 2 {
            return RefClause::UnitClause(self[ci].lits[(self[ci].lits[0] == p) as usize]);
        }
        self[ci].search_from = 0;
        let mut new_lits: Vec<Lit> = self[ci]
            .lits
            .iter()
            .filter(|&l| *l != p)
            .copied()
            .collect::<Vec<Lit>>();
        let len2 = new_lits.len() == 2;
        if len2 {
            if let Some(reg) = self.binary_link.search(new_lits[0], new_lits[1]) {
                return RefClause::RegisteredClause(reg);
            }
        }
        self.unweave(ci, 0);
        self.unweave(ci, 1);
        std::mem::swap(&mut self[ci].lits, &mut new_lits);
        self.weave(ci);
        if len2 {
            self.binary_link.add(self[ci].lits[0], self[ci].lits[1], ci);
            self.num_bi_clause += 1;
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
        let len2 = new_lits.len() == 2;
        if len2 {
            if let Some(did) = self.binary_link.search(new_lits[0], new_lits[1]) {
                if self.certification_store.is_active() {
                    self.certification_store.delete_clause(new_lits);
                }
                return RefClause::RegisteredClause(did);
            }
        }
        self.unweave(ci, 0);
        self.unweave(ci, 1);
        std::mem::swap(&mut self[ci].lits, new_lits);
        self.weave(ci);
        if len2 {
            let l0 = self[ci].lits[0];
            let l1 = self[ci].lits[1];
            self.binary_link.add(l0, l1, ci);
            self[ci].turn_off(FlagClause::LEARNT);
            self.num_bi_clause += 1;
        }
        if self.certification_store.is_active() {
            let ClauseDB {
                ref clause,
                ref mut certification_store,
                ..
            } = self;
            certification_store.add_clause(&clause[ci].lits);
            certification_store.delete_clause(&clause[ci].lits);
        }
        RefClause::Clause(ci)
    }
    // only used in `propagate_at_root_level`
    fn transform_by_simplification(
        &mut self,
        asg: &mut impl AssignIF,
        ci: ClauseIndex,
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
                    self.delete_clause(ci);
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
            n => {
                let l0 = new_lits[0];
                let l1 = new_lits[1];
                if n == 2 {
                    if let Some(bid) = self.binary_link.search(l0, l1) {
                        self.delete_clause(ci);
                        return RefClause::RegisteredClause(bid);
                    }
                }
                self.unweave(ci, 0);
                self.unweave(ci, 1);
                std::mem::swap(&mut self[ci].lits, &mut new_lits);
                self.weave(ci);
                if n == 2 {
                    self.binary_link.add(l0, l1, ci);
                    self.num_bi_clause += 1;
                    if self[ci].is(FlagClause::LEARNT) {
                        self.num_learnt -= 1;
                        self[ci].turn_off(FlagClause::LEARNT);
                    }
                }
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
    // used in `propagate`, `propagate_sandbox`, and `handle_conflict` for chrono_BT
    #[inline]
    fn transform_by_updating_watch(
        &mut self,
        wli: WatchLiteralIndex,
        new: usize,
    ) -> WatchLiteralIndex {
        let ret: WatchLiteralIndex = self.clause[wli.as_ci()].link[wli.as_wi()].next;
        self.reweave(wli.as_ci(), wli.as_wi(), new);
        // self.check_weave(wli.as_ci(), &[0, 1]);
        ret
    }
    fn update_at_analysis(&mut self, asg: &impl AssignIF, ci: ClauseIndex) -> bool {
        let ClauseDB {
            ref mut clause,
            ref mut lbd_temp,
            ..
        } = self;
        let c = &mut clause[ci];
        let rank: DecisionLevel = c.update_lbd(asg, lbd_temp);
        let learnt = c.is(FlagClause::LEARNT);
        if learnt {
            #[cfg(feature = "keep_just_used_clauses")]
            c.turn_on(FlagClause::NEW_CLAUSE);
            #[cfg(feature = "clause_rewarding")]
            self.reward_at_analysis(ci);
        }
        if 1 < rank {
            self.lb_entanglement.update(rank as f64);
        }
        learnt
    }
    /// reduce the number of 'learnt' or *removable* clauses.
    #[cfg(feature = "keep_just_used_clauses")]
    fn reduce(&mut self, asg: &mut impl AssignIF, threshold: f64) {
        impl Clause {
            fn extended_lbd(&self) -> f64 {
                let l: f64 = self.len() as f64;
                let r: f64 = self.rank as f64;
                r + (l - r) / (l - r + 1.0)
            }
        }
        // let ClauseDB {
        //     ref mut clause,
        //     ref mut lbd_temp,
        //     ref mut num_reduction,

        //     #[cfg(feature = "clause_rewarding")]
        //     ref tick,
        //     #[cfg(feature = "clause_rewarding")]
        //     ref activity_decay,
        //     ..
        // } = self;
        self.num_reduction += 1;
        // let mut keep: usize = 0;
        // let mut alives: usize = 0;
        // let mut perm: Vec<OrderedProxy<ClauseIndex>> = Vec::with_capacity(clause.len());
        // let reduction_threshold = self.reduction_threshold + 4;
        /* let reduction_threshold: DecisionLevel = 4
        + ((self
            .reduction_threshold
            .saturating_sub(self.lb_entanglement.get() as u32)
            + 1) as f64)
            .sqrt() as u32; */
        for ci in 1..self.clause.len() {
            if self.clause[ci].is_dead() {
                continue;
            }
            // alives += 1;
            // keep += 1;
            self.clause[ci].turn_off(FlagClause::NEW_CLAUSE);
            // if self.clause[ci].is(FlagClause::FORWD_LINK)
            //     || self.clause[ci].is(FlagClause::BCKWD_LINK)
            // {
            //     self.clause[ci].turn_off(FlagClause::FORWD_LINK);
            //     self.clause[ci].turn_off(FlagClause::BCKWD_LINK);
            //     continue;
            // }
            /* let fwd: bool = self.clause[ci].is(FlagClause::FORWD_LINK);
            self.clause[ci].turn_off(FlagClause::FORWD_LINK);
            if self.clause[ci].is(FlagClause::BCKWD_LINK) {
                self.clause[ci].turn_off(FlagClause::BCKWD_LINK);
                continue;
            } */
            if self.clause[ci].is(FlagClause::FORWD_LINK)
                || self.clause[ci].is(FlagClause::BCKWD_LINK)
            {
                self.clause[ci].turn_off(FlagClause::FORWD_LINK);
                self.clause[ci].turn_off(FlagClause::BCKWD_LINK);
                continue;
            }
            /* let bwd: bool = self.clause[ci].is(FlagClause::BCKWD_LINK);
            if bwd {
                self.clause[ci].turn_off(FlagClause::BCKWD_LINK);
            } */
            if self.clause[ci].is(FlagClause::LEARNT) {
                let ClauseDB {
                    ref mut clause,
                    ref mut lbd_temp,
                    ..
                } = self;
                if clause[ci].rank < threshold as DecisionLevel {
                    continue;
                }
                clause[ci].update_lbd(asg, lbd_temp);
                if threshold < clause[ci].extended_lbd() {
                    // keep -= 1;
                    // perm.push(OrderedProxy::new(ci, c.rank as f64));
                    self.delete_clause(ci);
                    continue;
                }
            }
        }
        // let keep = perm.len().max(alives);
        // if perm.is_empty() {
        //     return;
        // }
        // perm.sort();
        // let threshold = perm[keep.min(perm.len() - 1)].value();
        // for i in perm.iter().skip(keep) {
        //     // Being clause-position-independent, we keep or delete
        //     // all clauses that have a same value as a unit.
        //     if i.value() == threshold {
        //         continue;
        //     }
        //     self.delete_clause(i.to());
        // }
    }
    #[cfg(not(feature = "keep_just_used_clauses"))]
    #[allow(unreachable_code, unused_variables)]
    fn reduce(&mut self, asg: &mut impl AssignIF, setting: ReductionType) {
        impl Clause {
            fn reverse_activity_sum(&self, asg: &impl AssignIF) -> f64 {
                self.iter().map(|l| 1.0 - asg.activity(l.vi())).sum()
            }
            fn lbd(&self) -> f64 {
                self.rank as f64
            }
        }
        let ClauseDB {
            ref mut clause,
            ref mut lbd_temp,
            ref mut num_reduction,

            #[cfg(feature = "clause_rewarding")]
            ref tick,
            #[cfg(feature = "clause_rewarding")]
            ref activity_decay,
            ..
        } = self;
        *num_reduction += 1;

        let mut perm: Vec<OrderedProxy<ClauseIndex>> = Vec::with_capacity(clause.len());
        let mut alives: i32 = 0;
        let force_to_update_lbd: bool = match setting {
            ReductionType::RASonADD(_) => false,
            ReductionType::RASonALL(_, _) => true,
            ReductionType::LBDonADD(_) => false,
            ReductionType::LBDonALL(_, _) => true,
            #[cfg(feature = "clause_rewarding")]
            ReductionType::ClauseActivity => false,
            #[cfg(feature = "keep_just_used_clauses")]
            ReductionType::ClauseUsed => false,
        };
        for (ci, c) in clause
            .iter_mut()
            .enumerate()
            .skip(1)
            .filter(|(_, c)| !c.is_dead())
        {
            if force_to_update_lbd {
                c.update_lbd(asg, lbd_temp);
            }

            if !c.is(FlagClause::LEARNT) {
                continue;
            }
            #[cfg(feature = "clause_rewarding")]
            c.update_activity(*tick, *activity_decay, 0.0);
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
                #[cfg(feature = "clause_rewarding")]
                ReductionType::ClauseActivity => perm.push(OrderedProxy::new(ci, -c.activity)),
                #[cfg(feature = "keep_just_used_clauses")]
                ReductionType::ClauseUsed => unreachable!(),
            }
        }
        let keep = match setting {
            ReductionType::RASonADD(size) => perm.len().saturating_sub(size),
            ReductionType::RASonALL(_, scale) => (perm.len() as f64).powf(1.0 - scale) as usize,
            ReductionType::LBDonADD(size) => perm.len().saturating_sub(size),
            ReductionType::LBDonALL(_, scale) => (perm.len() as f64).powf(1.0 - scale) as usize,
            #[cfg(feature = "clause_rewarding")]
            ReductionType::ClauseActivity => (perm.len() as f64).powf(0.75) as usize,
            #[cfg(feature = "keep_just_used_clauses")]
            ReductionType::ClauseUsed => unreachable!(),
        };
        if perm.is_empty() {
            return;
        }
        self.reduction_threshold = match setting {
            ReductionType::RASonADD(_) | ReductionType::RASonALL(_, _) => {
                keep as f64 / alives as f64
            }
            ReductionType::LBDonADD(_) | ReductionType::LBDonALL(_, _) => {
                -(keep as f64) / alives as f64
            }
            #[cfg(feature = "clause_rewarding")]
            ReductionType::ClauseActivity => keep as f64 / alives as f64,
            #[cfg(feature = "keep_just_used_clauses")]
            ReductionType::ClauseUsed => unreachable!(),
        };
        perm.sort();
        let threshold = perm[keep.min(perm.len() - 1)].value();
        for i in perm.iter().skip(keep) {
            // Being clause-position-independent, we keep or delete
            // all clauses that have a same value as a unit.
            if i.value() == threshold {
                continue;
            }
            self.delete_clause(i.to());
        }
    }
    fn reset(&mut self) {
        for ci in 1..self.len() {
            let c = &self.clause[ci];
            if c.is(FlagClause::LEARNT) && (self.co_lbd_bound as usize) < c.len() {
                self.delete_clause(ci);
            }
        }
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
    fn minimize_with_bi_clauses(&mut self, asg: &impl AssignIF, vec: &mut Vec<Lit>) {
        debug_assert!(1 < vec.len());
        self.lbd_temp[0] += 1;
        let key: usize = self.lbd_temp[0];
        for l in &vec[1..] {
            self.lbd_temp[l.vi()] = key;
        }
        let lit0 = vec[0];
        let mut num_sat = 0;
        for (other, _) in self.binary_link.iter(lit0) {
            let vi = other.vi();
            if self.lbd_temp[vi] == key && asg.assigned(*other) == Some(true) {
                num_sat += 1;
                self.lbd_temp[vi] = key - 1;
            }
        }
        if 0 < num_sat {
            self.lbd_temp[lit0.vi()] = key;
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
        for (other, _) in self.binary_link.iter(lit) {
            // [!other, third]
            for (third, _) in self.binary_link.iter(!*other) {
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
    fn link_to_cid(&self, l0: Lit, l1: Lit) -> Option<ClauseIndex> {
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

// valid (encoded) lits start from 2. So we have two extra room.
const FREE_LIT: usize = 1; // == usize::from(!Lit::default())

// Clauses have two watches. We use the second watch holder to chain free clauses
const FREE_WATCH_INDEX: usize = 1;
const NEFR_WATCH_INDEX: usize = 0;

impl ClauseWeaverIF for ClauseDB {
    fn weave(&mut self, ci: ClauseIndex) {
        // attach each watch literal to watcher list
        if self.clause[ci].len() < 4 {
            for wi in 0..=1 {
                let lit: usize = usize::from(!self.clause[ci].lits[wi]);
                let wli = WatchLiteralIndex::new(ci, wi);
                let head: &mut WatchLiteralIndexRef = &mut self.watch[lit];
                let next: WatchLiteralIndex = head.next;
                debug_assert_ne!(next, wli);
                head.next = wli;
                self.clause[ci].link[wi].prev = WatchLiteralIndex::default();
                self.clause[ci].link[wi].next = next;
                if next.is_none() {
                    head.prev = wli;
                } else {
                    self.clause[next.as_ci()].link[next.as_wi()].prev = wli;
                }
                debug_assert!(
                    (self.clause[ci].link[wi].prev != self.clause[ci].link[wi].next)
                        || (self.clause[ci].link[wi].prev == WatchLiteralIndex::default()
                            && self.clause[ci].link[wi].next == WatchLiteralIndex::default())
                );
            }
        } else {
            for wi in 0..=1 {
                let lit: usize = usize::from(!self.clause[ci].lits[wi]);
                let wli = WatchLiteralIndex::new(ci, wi);
                let head: &mut WatchLiteralIndexRef = &mut self.watch[lit];
                let prev: WatchLiteralIndex = head.prev;
                debug_assert_ne!(prev, wli);
                head.prev = wli;
                self.clause[ci].link[wi].prev = prev;
                self.clause[ci].link[wi].next = WatchLiteralIndex::default();
                if prev.is_none() {
                    head.next = wli;
                } else {
                    self.clause[prev.as_ci()].link[prev.as_wi()].next = wli;
                }
                debug_assert!(
                    (self.clause[ci].link[wi].prev != self.clause[ci].link[wi].next)
                        || (self.clause[ci].link[wi].prev == WatchLiteralIndex::default()
                            && self.clause[ci].link[wi].next == WatchLiteralIndex::default())
                );
            }
        }
        debug_assert_ne!(self.clause[ci].lit0(), Lit::default());
        debug_assert_ne!(self.clause[ci].lit1(), Lit::default());
        // self.check_weave(ci, &[0, 1]);
    }
    fn unweave(&mut self, ci: ClauseIndex, wi: usize) {
        debug_assert!(wi < 2);
        let WatchLiteralIndexRef { prev, next } = self.clause[ci].link[wi];
        let lit: usize = usize::from(!self.clause[ci].lits[wi]);
        if prev.is_none() {
            self.watch[lit].next = next;
        } else {
            self.clause[prev.as_ci()].link[prev.as_wi()].next = next;
        }
        if next.is_none() {
            self.watch[lit].prev = prev;
        } else {
            self.clause[next.as_ci()].link[next.as_wi()].prev = prev;
        }
    }
    fn reweave(&mut self, ci: ClauseIndex, wi: usize, wj: usize) {
        debug_assert!(wi < 2);
        debug_assert!((wi == 1 && wj == 1) || 2 <= wj, "not {wi} < {wj}");
        // 1. unlink wi
        let WatchLiteralIndexRef { prev, next } = self.clause[ci].link[wi];
        let lit: usize = usize::from(!self.clause[ci].lits[wi]);
        if prev.is_none() {
            self.watch[lit].next = next;
        } else {
            self.clause[prev.as_ci()].link[prev.as_wi()].next = next;
        }
        if next.is_none() {
            self.watch[lit].prev = prev;
        } else {
            self.clause[next.as_ci()].link[next.as_wi()].prev = prev;
        }
        // 2. swap two literals
        let lit: usize = if wi == wj {
            debug_assert_eq!(wi, 1);

            // if self.clause[ci].lits[FREE_WATCH_INDEX] == Lit::default() {
            //     dbg!(ci, &self.clause[ci]);
            // }
            debug_assert_ne!(
                self.clause[ci].lits[FREE_WATCH_INDEX],
                Lit::default(),
                "{ci}: self.clause[ci].lits[FREE_WATCH_INDEX]{}",
                self.clause[ci].lits[FREE_WATCH_INDEX]
            );
            self.clause[ci].lits[FREE_WATCH_INDEX] = Lit::default();
            FREE_LIT
        } else {
            self.clause[ci].lits.swap(wi, wj);
            usize::from(!self.clause[ci].lits[wi])
        };
        // 3. link to watch list by new wi
        let wli = WatchLiteralIndex::new(ci, wi);
        let head: &mut WatchLiteralIndexRef = &mut self.watch[lit];
        if self.clause[ci].rank <= 2 {
            let next: WatchLiteralIndex = head.next;
            head.next = wli;
            self.clause[ci].link[wi].prev = WatchLiteralIndex::default();
            self.clause[ci].link[wi].next = next;
            if next.is_none() {
                head.prev = wli;
            } else {
                self.clause[next.as_ci()].link[next.as_wi()].prev = wli;
            }
            debug_assert!(
                (self.clause[ci].link[wi].prev != self.clause[ci].link[wi].next)
                    || (self.clause[ci].link[wi].prev == WatchLiteralIndex::default()
                        && self.clause[ci].link[wi].next == WatchLiteralIndex::default())
            );
        } else {
            let prev: WatchLiteralIndex = head.prev;
            head.prev = wli;
            self.clause[ci].link[wi].prev = prev;
            self.clause[ci].link[wi].next = WatchLiteralIndex::default();
            if prev.is_none() {
                head.next = wli;
            } else {
                self.clause[prev.as_ci()].link[prev.as_wi()].next = wli;
            }
            debug_assert!(
                (self.clause[ci].link[wi].prev != self.clause[ci].link[wi].next)
                    || (self.clause[ci].link[wi].prev == WatchLiteralIndex::default()
                        && self.clause[ci].link[wi].next == WatchLiteralIndex::default())
            );
        }
        // self.check_weave(ci, &[wi]);
    }
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<WatchLiteralIndexRef> {
        // ci 0 must refer to the header
        let nc = clauses.len();
        for (ci, c) in clauses.iter_mut().enumerate().skip(1) {
            c.link[FREE_WATCH_INDEX].set(
                WatchLiteralIndex::new(ci - 1, FREE_WATCH_INDEX),
                WatchLiteralIndex::new((ci + 1) % nc, FREE_WATCH_INDEX),
            );
            debug_assert_eq!(c.lits[1], Lit::default());
        }
        let mut watches = vec![WatchLiteralIndexRef::default(); 2 * (num_vars + 1)];
        if 1 < nc {
            clauses[1].link[FREE_WATCH_INDEX].prev = WatchLiteralIndex::default();
            clauses[nc - 1].link[FREE_WATCH_INDEX].next = WatchLiteralIndex::default();
            watches[FREE_LIT].set(
                WatchLiteralIndex::new(nc - 1, FREE_WATCH_INDEX),
                WatchLiteralIndex::new(1, FREE_WATCH_INDEX),
            );
        }
        watches
    }
    fn get_first_watch(&mut self, lit: Lit) -> WatchLiteralIndex {
        self.watch[usize::from(lit)].next
    }
    fn get_free_index(&mut self) -> ClauseIndex {
        let next: WatchLiteralIndex = self.watch[FREE_LIT].next;
        if next.is_none() {
            self.clause.push(Clause::default());
            // assert_ne!(1, self.clause.len());
            self.clause.len() - 1
        } else {
            // self.check_weave(next.as_ci(), &[FREE_WATCH_INDEX]);
            self.unweave(next.as_ci(), FREE_WATCH_INDEX);
            // self.watch[FREE_LIT].next = self.clause[next.as_ci()].links[next.as_wi()].next;
            // let prev: &mut WatchLiteralIndex = &mut self.watch[FREE_LIT].prev;
            // if *prev == next {
            //     *prev = WatchLiteralIndex::default();
            // }
            debug_assert_eq!(
                self.clause[next.as_ci()].lits[FREE_WATCH_INDEX],
                Lit::default(),
            );
            debug_assert_ne!(next, self.watch[FREE_LIT].next);
            debug_assert_ne!(0, next.as_ci());
            let ci = next.as_ci();
            self.clause[ci].rank = u32::MAX;
            self.clause[ci].rank_old = u32::MAX;
            ci
        }
    }
    // Check whether a zombi exists
    /* fn check(&self) {
        let mut deads: HashSet<ClauseIndex> = HashSet::new();
        let mut wli = self.watch[FREE_LIT].next;
        while !wli.is_none() {
            deads.insert(wli.as_ci());
            wli = self.clause[wli.as_ci()].link[wli.as_wi()].next;
        }
        assert!(self
            .clause
            .iter()
            .enumerate()
            .skip(1)
            .all(|(ci, c)| c.is_dead() || deads.contains(&ci)));
    } */
}

impl ClauseDB {
    #[allow(dead_code)]
    fn check_weave(&self, ci: ClauseIndex, v: &[usize]) {
        const RED: &str = "\x1B[001m\x1B[031m";
        const GREEN: &str = "\x1B[001m\x1B[032m";
        const BLUE: &str = "\x1B[001m\x1B[034m";
        const RESET: &str = "\x1B[000m";
        for i in v.iter() {
            let lit: usize = usize::from(!self.clause[ci].lits[*i]);
            let mut ptr = self.watch[lit].next;
            let mut found = false;
            let mut forward = 0;
            while !ptr.is_none() {
                assert!(
                    lit == FREE_WATCH_INDEX
                        || self.clause[ptr.as_ci()].lits[ptr.as_wi()] != Lit::default(),
                    "{GREEN}c{ci}{:?} has a zero!{RESET}",
                    self.clause[ptr.as_ci()]
                );
                assert!(ptr.as_ci() != 0 || ptr.as_wi() == 0);
                if ptr.as_ci() == ci {
                    found = true;
                }
                ptr = self.clause[ptr.as_ci()].link[ptr.as_wi()].next;
                forward += 1;
                assert!(
                    forward < 10000,
                    "{GREEN}forward weave {lit} has a loop!{RESET}"
                );
            }
            assert!(
                found,
                "{RED}{}: {:?} is not in forward weave {}{RESET}",
                ci, &self.clause[ci], lit
            );
            if lit == 1 {
                continue;
            }
            let mut ptr = self.watch[lit].prev;
            let mut found = false;
            let mut backward = 0;
            while !ptr.is_none() {
                assert!(ptr.as_ci() != 0 || ptr.as_wi() == 0);
                if ptr.as_ci() == ci {
                    found = true;
                }
                ptr = self.clause[ptr.as_ci()].link[ptr.as_wi()].prev;
                backward += 1;
                assert!(
                    backward < 10000,
                    "{RED}backward weave {lit} has a loop!{RESET}"
                );
            }
            assert!(
                found,
                "{BLUE}ci {}:{:?} is not in backward weave {} (head: {:?}){RESET}",
                ci, &self.clause[ci], lit, self.watch[lit]
            );
            assert_eq!(
                forward, backward,
                "{GREEN}weave {lit} forward length {forward}, backward length {backward}\nAfter {ci} modification: {:?}{RESET}",
                &self.clause[ci]
            )
        }
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
    #[cfg(feature = "clause_rewarding")]
    ClauseActivity,
    #[cfg(feature = "keep_just_used_clauses")]
    ClauseUsed,
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
    }

    pub const F64: [Tf64; 2] = [Tf64::LiteralBlockDistance, Tf64::LiteralBlockEntanglement];

    impl PropertyDereference<Tf64, f64> for ClauseDB {
        #[inline]
        fn derefer(&self, k: Tf64) -> f64 {
            match k {
                Tf64::LiteralBlockDistance => self.lbd.get(),
                Tf64::LiteralBlockEntanglement => self.lb_entanglement.get(),
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
        #[cfg(feature = "keep_just_used_clauses")]
        assert!(c.is(FlagClause::NEW_CLAUSE));
        let c2 = cdb
            .new_clause(&mut asg, &mut vec![lit(-1), lit(2), lit(3)], true)
            .as_ci();
        let c = &cdb[c2];
        assert!(!c.is_dead());
        assert!(c.is(FlagClause::LEARNT));
        #[cfg(feature = "keep_just_used_clauses")]
        assert!(c.is(FlagClause::NEW_CLAUSE));
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
        assert_eq!(cdb[c1][0..].iter().map(|l| i32::from(*l)).sum::<i32>(), 6);
        let mut iter = cdb[c1][0..].iter();
        assert_eq!(iter.next(), Some(&lit(1)));
        assert_eq!(iter.next(), Some(&lit(2)));
        assert_eq!(iter.next(), Some(&lit(3)));
        assert_eq!(iter.next(), None);
    }
}

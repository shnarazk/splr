use {
    super::{
        binary::{BinaryLinkIF, BinaryLinkList},
        ema::ProgressLBD,
        property,
        watch_cache::*,
        BinaryLinkDB, CertificationStore, Clause, ClauseDB, ClauseDBIF, ClauseId, ClauseRef,
        ClauseRefIF, ReductionType, RefClause,
    },
    crate::{assign::AssignIF, types::*},
    std::{
        cell::RefCell,
        iter::Iterator,
        num::NonZeroU32,
        ops::Index,
        // slice::{Iter as SliceIter, IterMut as SliceIterMut},
    },
};

#[cfg(not(feature = "no_IO"))]
use std::{fs::File, io::Write, path::Path};

impl Default for ClauseDB {
    fn default() -> ClauseDB {
        ClauseDB {
            clause: Vec::new(),
            binary_link: BinaryLinkDB::default(),
            watch_cache: Vec::new(),
            freelist: Vec::new(),
            certification_store: CertificationStore::default(),
            soft_limit: 0, // 248_000_000
            co_lbd_bound: 4,
            bi_clause_completion_queue: Vec::new(),
            num_bi_clause_completion: 0,
            // lbd_frozen_clause: 30,
            #[cfg(feature = "clause_rewarding")]
            tick: 0,
            #[cfg(feature = "clause_rewarding")]
            activity_decay: 0.99,
            #[cfg(feature = "clause_rewarding")]
            activity_anti_decay: 0.01,

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
            eliminated_permanent: Vec::new(),
        }
    }
}

impl Index<ClauseId> for ClauseDB {
    type Output = RefCell<Clause>;
    #[inline]
    fn index(&self, cid: ClauseId) -> &RefCell<Clause> {
        let i = NonZeroU32::get(cid.ordinal) as usize;
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked(i).get()
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.clause[i].get()
    }
}

// impl IndexMut<ClauseId> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, cid: ClauseId) -> &mut RefCell<Clause> {
//         let i = NonZeroU32::get(cid.ordinal) as usize;
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             &mut self.clause.get_unchecked_mut(i).get()
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self.clause[i].get()
//     }
// }

impl Index<&ClauseId> for ClauseDB {
    type Output = RefCell<Clause>;
    #[inline]
    fn index(&self, cid: &ClauseId) -> &RefCell<Clause> {
        let i = NonZeroU32::get(cid.ordinal) as usize;
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked(i).get()
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.clause[i].get()
    }
}

// impl IndexMut<&ClauseId> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, cid: &ClauseId) -> &mut ClauseRef {
//         let i = NonZeroU32::get(cid.ordinal) as usize;
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.clause.get_unchecked_mut(i)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self.clause[i]
//     }
// }

// impl Index<Range<usize>> for ClauseDB {
//     type Output = [RefCell<Clause>];
//     #[inline]
//     fn index(&self, r: Range<usize>) -> &[RefCell<Clause>] {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.clause.get_unchecked(r).map(|cr| cr.get())
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self.clause[r].get()
//     }
// }

// impl Index<RangeFrom<usize>> for ClauseDB {
//     type Output = [RefCell<Clause>];
//     #[inline]
//     fn index(&self, r: RangeFrom<usize>) -> &[RefCell<Clause>] {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.clause.get_unchecked(r)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self.clause[r]
//     }
// }

// impl IndexMut<Range<usize>> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, r: Range<usize>) -> &mut [Clause] {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.clause.get_unchecked_mut(r)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self.clause[r]
//     }
// }

// impl IndexMut<RangeFrom<usize>> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Clause] {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.clause.get_unchecked_mut(r)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self.clause[r]
//     }
// }

impl Instantiate for ClauseDB {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> ClauseDB {
        let nv = cnf.num_of_variables;
        let nc = cnf.num_of_clauses;
        let mut clause = Vec::with_capacity(1 + nc);
        let mut c = Clause::default();
        c.turn_on(FlagClause::DEAD);
        let cr = ClauseRef::new(c);
        clause.push(cr);
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        for _ in 0..2 * (nv + 1) {
            watcher.push(WatchCache::new());
        }
        ClauseDB {
            clause,
            binary_link: BinaryLinkDB::instantiate(config, cnf),
            watch_cache: watcher,
            certification_store: CertificationStore::instantiate(config, cnf),
            soft_limit: config.c_cls_lim,
            lbd: ProgressLBD::instantiate(config, cnf),

            #[cfg(feature = "clause_rewarding")]
            activity_decay: config.crw_dcy_rat,
            #[cfg(feature = "clause_rewarding")]
            activity_anti_decay: 1.0 - config.crw_dcy_rat,

            ..ClauseDB::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        #[allow(clippy::single_match)]
        match e {
            SolverEvent::Assert(_) => {
                self.lbd.update(0);
            }
            SolverEvent::NewVar => {
                self.binary_link.add_new_var();
                // for negated literal
                self.watch_cache.push(WatchCache::new());
                // for positive literal
                self.watch_cache.push(WatchCache::new());
            }
            SolverEvent::Restart => {
                // self.lbd.reset_to(self.lb_entanglement.get());
                // self.lbd.reset_to(0.0);
            }
            _ => (),
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
    fn iter(&self) -> impl Iterator<Item = &RefCell<Clause>> {
        self.clause
            .iter()
            .filter(|cr| {
                let rcc = cr.get();
                let c = rcc.borrow();
                !c.is_dead()
            })
            .map(|cr| cr.get())
    }
    // fn iter_mut(&mut self) -> IterMut<'_, Clause> {
    //     self.clause.iter_mut()
    // }
    #[inline]
    fn binary_links(&self, l: Lit) -> &BinaryLinkList {
        self.binary_link.connect_with(l)
    }
    // watch_cache_IF
    fn fetch_watch_cache_entry(&self, lit: Lit, wix: WatchCacheProxy) -> (ClauseId, Lit) {
        self.watch_cache[lit][wix]
    }
    #[inline]
    fn watch_cache_iter(&mut self, l: Lit) -> WatchCacheIterator {
        // let mut empty = WatchCache::new();
        // std::mem::swap(&mut self.watch_cache[l], &mut empty);
        // empty
        WatchCacheIterator::new(self.watch_cache[l].len())
    }
    fn detach_watch_cache(&mut self, l: Lit, iter: &mut WatchCacheIterator) {
        self.watch_cache[l].swap_remove(iter.index);
        iter.detach_entry();
    }
    fn merge_watch_cache(&mut self, p: Lit, wc: WatchCache) {
        self.watch_cache[p].append_watch(wc);
    }
    fn swap_watch(&mut self, cid: ClauseId) {
        let rcc = &self[cid];
        let mut c = rcc.borrow_mut();
        c.lits.swap(0, 1);
    }
    fn new_clause(
        &mut self,
        asg: &mut impl AssignIF,
        vec: &mut Vec<Lit>,
        learnt: bool,
    ) -> RefClause {
        debug_assert!(!vec.is_empty());
        debug_assert!(1 < vec.len());
        debug_assert!(vec.iter().all(|l| !vec.contains(&!*l)), "{vec:?}");
        if vec.len() == 2 {
            if let Some(&cid) = self.link_to_cid(vec[0], vec[1]) {
                self.num_reregistration += 1;
                return RefClause::RegisteredClause(cid);
            }
        }
        self.certification_store.add_clause(vec);
        let (cid, cr) = if let Some(cid_used) = self.freelist.pop() {
            let cr = &self.clause[usize::from(cid_used)];
            let rcc = cr.get();
            let mut c = rcc.borrow_mut();
            // if !c.is_dead() {
            //     println!("{} {:?}", cid.format(), vec2int(&c.lits));
            //     println!("len {}", self.watcher[NULL_LIT.negate() as usize].len());
            //     for w in &self.watcher[NULL_LIT.negate() as usize][..10] {
            //         if !self.clause[w.c].is_dead() {
            //             println!("{}", w.c.format());
            //         }
            //     }
            //     panic!("done");
            // }
            // assert!(c.is_dead());
            c.flags = FlagClause::empty();

            #[cfg(feature = "clause_rewarding")]
            {
                c.reward = 0.0;
            }

            debug_assert!(c.lits.is_empty()); // c.lits.clear();
            std::mem::swap(&mut c.lits, vec);
            c.search_from = 2;
            drop(c);
            (cid_used, cr)
        } else {
            let cid = ClauseId::from(self.clause.len());

            let mut c = Clause {
                flags: FlagClause::empty(),
                ..Clause::default()
            };
            std::mem::swap(&mut c.lits, vec);
            let cr = ClauseRef::new(c);
            self.clause.push(cr);
            let cr = self.clause.last().unwrap();
            (cid, cr)
        };

        let ClauseDB {
            #[cfg(feature = "bi_clause_completion")]
            ref mut bi_clause_completion_queue,
            // ref mut clause,
            ref mut num_clause,
            ref mut num_bi_clause,
            ref mut num_bi_learnt,
            ref mut num_lbd2,
            ref mut num_learnt,
            ref mut binary_link,

            #[cfg(feature = "clause_rewarding")]
            ref tick,

            ref mut watch_cache,
            ..
        } = self;
        // let c = &mut clause[NonZeroU32::get(cid.ordinal) as usize];
        let rcc = cr.get();
        let mut c = rcc.borrow_mut();
        #[cfg(feature = "clause_rewarding")]
        {
            c.timestamp = *tick;
        }
        let len2 = c.lits.len() == 2;
        if len2 {
            c.rank = 1;
            c.rank_old = 1;

            #[cfg(feature = "bi_clause_completion")]
            if learnt {
                for lit in c.iter() {
                    if !bi_clause_completion_queue.contains(lit) {
                        bi_clause_completion_queue.push(*lit);
                    }
                }
            }
        } else {
            c.update_lbd(asg);
            c.rank_old = c.rank;
        }
        self.lbd.update(c.rank);
        *num_clause += 1;
        if learnt {
            if len2 {
                *num_bi_learnt += 1;
            } else {
                c.turn_on(FlagClause::LEARNT);
                *num_learnt += 1;
                if c.rank <= 2 {
                    *num_lbd2 += 1;
                }
            }
        }
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        if len2 {
            *num_bi_clause += 1;
            binary_link.add(l0, l1, cid);
        } else {
            watch_cache[!l0].insert_watch(cid, l1);
            watch_cache[!l1].insert_watch(cid, l0);
        }
        RefClause::Clause(cid)
    }
    fn new_clause_sandbox(&mut self, asg: &mut impl AssignIF, vec: &mut Vec<Lit>) -> RefClause {
        debug_assert!(1 < vec.len());
        if vec.len() == 2 {
            if let Some(&cid) = self.link_to_cid(vec[0], vec[1]) {
                return RefClause::RegisteredClause(cid);
            }
        }
        let (cid, cr) = if let Some(cid_used) = self.freelist.pop() {
            let cr = &self.clause[usize::from(cid_used)];
            let rcc = cr.get();
            let mut c = rcc.borrow_mut();
            c.flags = FlagClause::empty();
            std::mem::swap(&mut c.lits, vec);
            c.search_from = 2;
            drop(rcc);
            drop(c);
            (cid_used, cr)
        } else {
            let mut c = Clause {
                flags: FlagClause::empty(),
                ..Clause::default()
            };
            std::mem::swap(&mut c.lits, vec);
            self.clause.push(ClauseRef::new(c));
            (
                ClauseId::from(self.clause.len()),
                self.clause.last().unwrap(),
            )
        };
        let rcc = cr.get();
        let mut c = rcc.borrow_mut();

        let ClauseDB {
            // ref mut clause,
            ref mut binary_link,
            #[cfg(feature = "clause_rewarding")]
            ref tick,
            ref mut watch_cache,
            ..
        } = self;
        // let c = &mut clause[NonZeroU32::get(cid.ordinal) as usize];

        #[cfg(feature = "clause_rewarding")]
        {
            c.timestamp = *tick;
        }

        let len2 = c.lits.len() == 2;
        if len2 {
            c.rank = 1;
            c.rank_old = 1;
        } else {
            c.update_lbd(asg);
            c.rank_old = c.rank;
            c.turn_on(FlagClause::LEARNT);
        }
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        if len2 {
            binary_link.add(l0, l1, cid);
        } else {
            watch_cache[!l0].insert_watch(cid, l1);
            watch_cache[!l1].insert_watch(cid, l0);
        }
        RefClause::Clause(cid)
    }
    /// ## Warning
    /// this function is the only function that makes dead clauses
    fn remove_clause(&mut self, cid: ClauseId) {
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
        // if !self.clause[NonZeroU32::get(cid.ordinal) as usize].is_dead() {
        // }
        let cr = &mut self.clause[NonZeroU32::get(cid.ordinal) as usize];
        let rcc = cr.get();
        let c = rcc.borrow_mut();

        debug_assert!(!c.is_dead());
        debug_assert!(1 < c.lits.len());
        let f = remove_clause_fn(
            &mut self.certification_store,
            &mut self.binary_link,
            &mut self.watch_cache,
            &mut self.num_bi_clause,
            &mut self.num_clause,
            &mut self.num_learnt,
            cid,
            cr,
        );
        self.freelist.push(f);
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
    }
    fn remove_clause_sandbox(&mut self, cid: ClauseId) {
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
        // let c = &mut self.clause[NonZeroU32::get(cid.ordinal) as usize];
        let cr = &mut self.clause[NonZeroU32::get(cid.ordinal) as usize];
        let rcc = cr.get();
        let c = rcc.borrow_mut();
        debug_assert!(!c.is_dead());
        debug_assert!(1 < c.lits.len());
        let mut store = CertificationStore::default();
        let mut dummy1 = 1;
        let mut dummy2 = 1;
        let mut dummy3 = 1;
        let f = remove_clause_fn(
            &mut store,
            &mut self.binary_link,
            &mut self.watch_cache,
            &mut dummy1,
            &mut dummy2,
            &mut dummy3,
            cid,
            cr,
        );
        self.freelist.push(f);
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
    }
    //
    fn transform_by_restoring_watch_cache(
        &mut self,
        l: Lit,
        iter: &mut WatchCacheIterator,
        op: Option<Lit>,
    ) {
        if let Some(p) = op {
            self.watch_cache[l][iter.index].1 = p;
        }

        // let cid = self.watch_cache[l][iter.index].0;
        // let c = &self[cid];
        // let l0 = c.lits[0];
        // let l1 = c.lits[1];
        // assert!(self.watch_cache[!l0].iter().any(|wc| wc.0 == cid && wc.1 == l1));
        // assert!(self.watch_cache[!l1].iter().any(|wc| wc.0 == cid && wc.1 == l0));

        iter.restore_entry();
    }
    // return a Lit if the clause becomes a unit clause.
    fn transform_by_elimination(&mut self, cid: ClauseId, p: Lit) -> RefClause {
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
        let rcc = self[cid].clone();
        let mut c = rcc.borrow_mut();
        let ClauseDB {
            // ref mut clause,
            ref mut binary_link,
            ref mut watch_cache,
            ref mut certification_store,
            ref mut num_bi_clause,
            ..
        } = self;
        debug_assert!(!c.is_dead());
        debug_assert!(1 < c.len());
        // debug_assert!((*ch).lits.contains(&p));
        // debug_assert!(1 < (*ch).len());
        debug_assert!(1 < usize::from(!p));
        debug_assert!(1 < c.lits.len());
        //
        //## Case:2-0
        //
        if c.lits.len() == 2 {
            if c.lits[0] == p {
                c.lits.swap(0, 1);
            }
            return RefClause::UnitClause(c.lits[0]);
        }

        c.search_from = 2;
        let lits = &mut c.lits;
        let mut new_lits: Vec<Lit> = lits
            .iter()
            .filter(|&l| *l != p)
            .copied()
            .collect::<Vec<Lit>>();
        if new_lits.len() == 2 {
            if let Some(&reg) = binary_link.search(new_lits[0], new_lits[1]) {
                //
                //## Case:3-0
                //
                return RefClause::RegisteredClause(reg);
            }
            //
            //## Case:3-2
            //
            let l0 = lits[0];
            let l1 = lits[1];
            std::mem::swap(lits, &mut new_lits);
            watch_cache[!l0].remove_watch(&cid);
            watch_cache[!l1].remove_watch(&cid);
            binary_link.add(lits[0], lits[1], cid);
            *num_bi_clause += 1;
            // self.watches(cid, "after strengthen_by_elimination case:3-2");
        } else {
            let old_l0 = lits[0];
            let old_l1 = lits[1];
            std::mem::swap(lits, &mut new_lits);
            let l0 = lits[0];
            let l1 = lits[1];
            //
            //## Case:3-3
            //

            // Here we assumed that there's no eliminated var in clause and *watch cache*.
            // Fortunately the current implementation purges all eliminated vars fully.
            if p == old_l0 {
                watch_cache[!p].remove_watch(&cid);
                if old_l1 == l0 {
                    debug_assert!(watch_cache[!l1].iter().all(|e| e.0 != cid));
                    watch_cache[!l1].insert_watch(cid, l0);

                    #[cfg(feature = "maintain_watch_cache")]
                    {
                        watch_cache[!l0].update_watch(cid, l1);
                    }
                } else if old_l1 == l1 {
                    debug_assert!(watch_cache[!l0].iter().all(|e| e.0 != cid));
                    watch_cache[!l0].insert_watch(cid, l1);

                    #[cfg(feature = "maintain_watch_cache")]
                    {
                        watch_cache[!l1].update_watch(cid, l0);
                    }
                } else {
                    unreachable!("transform_by_elimination");
                }
            } else if p == old_l1 {
                watch_cache[!p].remove_watch(&cid);
                if old_l0 == l0 {
                    debug_assert!(watch_cache[!l1].iter().all(|e| e.0 != cid));
                    watch_cache[!l1].insert_watch(cid, l0);

                    #[cfg(feature = "maintain_watch_cache")]
                    {
                        watch_cache[!l0].update_watch(cid, l1);
                    }
                } else if old_l0 == l1 {
                    debug_assert!(watch_cache[!l0].iter().all(|e| e.0 != cid));
                    watch_cache[!l0].insert_watch(cid, l1);

                    #[cfg(feature = "maintain_watch_cache")]
                    {
                        watch_cache[!l1].update_watch(cid, l0);
                    }
                } else {
                    unreachable!("transform_by_elimination");
                }
            } else {
                debug_assert_eq!(old_l0, l0);
                debug_assert_eq!(old_l1, l1);
            }

            #[cfg(feature = "maintain_watch_cache")]
            {
                debug_assert!(watch_cache[!c.lits[0]]
                    .iter()
                    .any(|wc| wc.0 == cid && wc.1 == c.lits[1]));
                debug_assert!(watch_cache[!c.lits[1]]
                    .iter()
                    .any(|wc| wc.0 == cid && wc.1 == c.lits[0]));
            }

            // self.watches(cid, "after strengthen_by_elimination case:3-3");
        }
        if certification_store.is_active() {
            certification_store.add_clause(&c.lits);
            certification_store.delete_clause(&new_lits);
        }
        RefClause::Clause(cid)
    }
    // Not in use so far
    fn transform_by_replacement(&mut self, cid: ClauseId, new_lits: &mut Vec<Lit>) -> RefClause {
        debug_assert!(1 < new_lits.len());
        //
        //## Clause transform rules
        //
        // There are three cases:
        // 1. a normal clause is merged to a registered bi-clause. [Case:0]
        // 2. a normal clause becomes a new bi-clause.             [Case:2]
        // 3. a normal clause becomes a shorter normal clause.     [Case:3]
        //
        let ClauseDB {
            clause,
            binary_link,
            watch_cache,
            certification_store,
            ..
        } = self;
        let rcc = &clause[usize::from(cid)].get();
        let mut c = rcc.borrow_mut();
        debug_assert!(!c.is_dead());
        // let c = &mut clause[NonZeroU32::get(cid.ordinal) as usize];
        debug_assert!(new_lits.len() < c.len());
        if new_lits.len() == 2 {
            if let Some(&did) = binary_link.search(new_lits[0], new_lits[1]) {
                //
                //## Case:0
                //
                if certification_store.is_active() {
                    certification_store.delete_clause(new_lits);
                }
                return RefClause::RegisteredClause(did);
            }
            //
            //## Case:2
            //
            let old_l0 = c.lit0();
            let old_l1 = c.lit0();
            std::mem::swap(&mut c.lits, new_lits);
            let l0 = c.lit0();
            let l1 = c.lit0();
            watch_cache[!old_l0].remove_watch(&cid);
            watch_cache[!old_l1].remove_watch(&cid);
            binary_link.add(l0, l1, cid);

            if certification_store.is_active() {
                certification_store.add_clause(new_lits);
                certification_store.delete_clause(&c.lits);
            }
            c.turn_off(FlagClause::LEARNT);
            self.num_bi_clause += 1;

            if certification_store.is_active() {
                certification_store.add_clause(&c.lits);
                certification_store.delete_clause(new_lits);
            }
        } else {
            //
            //## Case:3
            //
            let old_l0 = c.lit0();
            let old_l1 = c.lit0();
            std::mem::swap(&mut c.lits, new_lits);
            let l0 = c.lit0();
            let l1 = c.lit0();

            if (l0 == old_l0 && l1 == old_l1) || (l0 == old_l1 && l1 == old_l0) {
            } else if l0 == old_l0 {
                watch_cache[!old_l1].remove_watch(&cid);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cid));
                watch_cache[!l0].update_watch(cid, l1);
                // assert!(watch_cache[!l1].iter().all(|e| e.0 != cid));
                watch_cache[!l1].insert_watch(cid, l0);
            } else if l0 == old_l1 {
                watch_cache[!old_l0].remove_watch(&cid);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cid));
                watch_cache[!l0].update_watch(cid, l1);
                // assert!(watch_cache[!l1].iter().all(|e| e.0 != cid));
                watch_cache[!l1].insert_watch(cid, l0);
            } else if l1 == old_l0 {
                watch_cache[!old_l1].remove_watch(&cid);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cid));
                watch_cache[!l0].insert_watch(cid, l1);
                watch_cache[!l1].update_watch(cid, l0);
            } else if l1 == old_l1 {
                watch_cache[!old_l0].remove_watch(&cid);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cid));
                watch_cache[!l0].insert_watch(cid, l1);
                watch_cache[!l1].update_watch(cid, l0);
            } else {
                watch_cache[!old_l0].remove_watch(&cid);
                watch_cache[!old_l1].remove_watch(&cid);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cid));
                watch_cache[!l0].insert_watch(cid, l1);
                // assert!(watch_cache[!l1].iter().all(|e| e.0 != cid));
                watch_cache[!l1].insert_watch(cid, l0);
            }

            // maintain_watch_literal \\ assert!(watch_cache[!c.lits[0]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[1]));
            // maintain_watch_literal \\ assert!(watch_cache[!c.lits[1]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[0]));

            if certification_store.is_active() {
                certification_store.add_clause(new_lits);
                certification_store.delete_clause(&c.lits);
            }
        }
        RefClause::Clause(cid)
    }
    // only used in `propagate_at_root_level`
    fn transform_by_simplification(&mut self, asg: &mut impl AssignIF, cid: ClauseId) -> RefClause {
        let rcc = &self[cid];
        let c = rcc.borrow();
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
        debug_assert!(!c.is_dead());
        // firstly sweep without consuming extra memory
        let mut need_to_shrink = false;
        for l in c.iter() {
            debug_assert!(!asg.var(l.vi()).is(FlagVar::ELIMINATED));
            match asg.assigned(*l) {
                Some(true) => {
                    drop(c);
                    self.remove_clause(cid);
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
            return RefClause::Clause(cid);
        }
        drop(c);
        let ClauseDB {
            clause,
            binary_link,
            watch_cache,
            certification_store,
            ..
        } = self;
        let rcc = &clause[usize::from(cid)].get();
        let mut c = rcc.borrow_mut();
        // let c = &mut clause[NonZeroU32::get(cid.ordinal) as usize];
        let mut new_lits = c
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
                debug_assert!(2 < c.lits.len());
                if let Some(&bid) = binary_link.search(l0, l1) {
                    //
                    //## Case:3-0
                    //
                    drop(c);
                    self.remove_clause(cid);
                    return RefClause::RegisteredClause(bid);
                }
                //
                //## Case:3-2
                //
                watch_cache[!c.lits[0]].remove_watch(&cid);
                watch_cache[!c.lits[1]].remove_watch(&cid);
                binary_link.add(l0, l1, cid);
                std::mem::swap(&mut c.lits, &mut new_lits);
                self.num_bi_clause += 1;
                if c.is(FlagClause::LEARNT) {
                    self.num_learnt -= 1;
                    c.turn_off(FlagClause::LEARNT);
                }

                if certification_store.is_active() {
                    certification_store.add_clause(&c.lits);
                    certification_store.delete_clause(&new_lits);
                }
                RefClause::Clause(cid)
            }
            _ => {
                //
                //## Case:3-3
                //
                let old_l0 = c.lit0();
                let old_l1 = c.lit1();
                std::mem::swap(&mut c.lits, &mut new_lits);
                let l0 = c.lit0();
                let l1 = c.lit1();

                if old_l0 == l0 && old_l1 == l1 {
                    #[cfg(feature = "maintain_watch_cache")]
                    {
                        watch_cache[!l0].update_watch(cid, l1);
                        watch_cache[!l1].update_watch(cid, l0);
                    }
                } else if old_l0 == l0 {
                    // assert_ne!(old_l1, l1);
                    watch_cache[!old_l1].remove_watch(&cid);
                    watch_cache[!l0].update_watch(cid, l1);
                    // assert!(watch_cache[!l1].iter().all(|e| e.0 != cid));
                    watch_cache[!l1].insert_watch(cid, l0);
                } else if old_l0 == l1 {
                    // assert_ne!(old_l1, l0);
                    watch_cache[!old_l1].remove_watch(&cid);
                    // assert!(watch_cache[!l0].iter().all(|e| e.0 != cid));
                    watch_cache[!l0].insert_watch(cid, l1);
                    watch_cache[!l1].update_watch(cid, l0);
                } else if old_l1 == l0 {
                    // assert_ne!(old_l0, l1);
                    watch_cache[!old_l0].remove_watch(&cid);
                    watch_cache[!l0].update_watch(cid, l1);
                    watch_cache[!l1].insert_watch(cid, l0);
                } else if old_l1 == l1 {
                    // assert_ne!(old_l0, l0);
                    watch_cache[!old_l0].remove_watch(&cid);
                    watch_cache[!l0].insert_watch(cid, l1);
                    watch_cache[!l1].update_watch(cid, l0);
                } else {
                    watch_cache[!old_l0].remove_watch(&cid);
                    watch_cache[!old_l1].remove_watch(&cid);
                    // assert!(watch_cache[!l0].iter().all(|e| e.0 != cid));
                    watch_cache[!l0].insert_watch(cid, l1);
                    // assert!(watch_cache[!l1].iter().all(|e| e.0 != cid));
                    watch_cache[!l1].insert_watch(cid, l0);
                }

                // maintain_watch_literal \\ assert!(watch_cache[!c.lits[0]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[1]));
                // maintain_watch_literal \\ assert!(watch_cache[!c.lits[1]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[0]));

                if certification_store.is_active() {
                    certification_store.add_clause(&c.lits);
                    certification_store.delete_clause(&new_lits);
                }
                RefClause::Clause(cid)
            }
        }
    }
    // used in `propagate`, `propagate_sandbox`, and `handle_conflict` for chronoBT
    fn transform_by_updating_watch(
        &mut self,
        cid: ClauseId,
        old: usize,
        new: usize,
        removed: bool,
    ) {
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

        let ClauseDB {
            ref clause,
            ref mut watch_cache,
            ..
        } = self;
        let rcc = clause[usize::from(cid)].get();
        let mut c = rcc.borrow_mut();
        debug_assert!(!c.is_dead());
        debug_assert!(old < 2);
        debug_assert!(1 < new);
        // let c = &mut clause[NonZeroU32::get(cid.ordinal) as usize];
        let other = (old == 0) as usize;
        if removed {
            debug_assert!(watch_cache[!c.lits[old]].get_watch(&cid).is_none());
        } else {
            //## Step:1
            let l = !c.lits[old];
            watch_cache[l].remove_watch(&cid);
        }
        //## Step:2
        // assert!(watch_cache[!c.lits[new]].iter().all(|e| e.0 != cid));
        let l = !c.lits[new];
        let k = c.lits[other];
        watch_cache[l].insert_watch(cid, k);

        #[cfg(feature = "maintain_watch_cache")]
        {
            //## Step:3
            watch_cache[!c.lits[other]].update_watch(cid, c.lits[new]);
        }

        c.lits.swap(old, new);

        // maintain_watch_literal \\ assert!(watch_cache[!c.lits[0]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[1]));
        // maintain_watch_literal \\ assert!(watch_cache[!c.lits[1]].iter().any(|wc| wc.0 == cid && wc.1 == c.lits[0]));
    }
    fn update_at_analysis(&mut self, asg: &impl AssignIF, cid: ClauseId) -> bool {
        // let c = &mut self.clause[NonZeroU32::get(cid.ordinal) as usize];
        let rcc = &self[cid];
        let mut c = rcc.borrow_mut();
        // Updating LBD at every analysis seems redundant.
        // But it's crucial. Don't remove the below.
        let rank = c.update_lbd(asg);
        let learnt = c.is(FlagClause::LEARNT);
        if learnt {
            #[cfg(feature = "just_used")]
            c.turn_on(FlagClause::USED);
            #[cfg(feature = "clause_rewading")]
            self.reward_at_analysis(cid);
        }
        drop(c);
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

        let mut perm: Vec<OrderedProxy<usize>> = Vec::with_capacity(clause.len());
        let mut alives = 0;
        for (i, cr) in clause.iter_mut().enumerate().skip(1).filter(|(_, cr)| {
            let rcc = cr.get();
            let c = rcc.borrow();
            !c.is_dead()
        }) {
            let rcc = cr.get();
            let mut c = rcc.borrow_mut();
            c.update_lbd(asg);

            #[cfg(feature = "clause_rewarding")]
            c.update_activity(*tick, *activity_decay, 0.0);

            // There's no clause stored in `reason` because the decision level is 'zero.'
            debug_assert_ne!(
                asg.reason(c.lit0().vi()),
                AssignReason::Implication(ClauseId::from(i)),
                "Lit {} {:?} level {}, dl: {}",
                i32::from(c.lit0()),
                asg.assigned(c.lit0()),
                asg.level(c.lit0().vi()),
                asg.decision_level(),
            );
            if !c.is(FlagClause::LEARNT) {
                continue;
            }
            alives += 1;
            match setting {
                ReductionType::RASonADD(_) => {
                    perm.push(OrderedProxy::new(i, c.reverse_activity_sum(asg)));
                }
                ReductionType::RASonALL(cutoff, _) => {
                    let value = c.reverse_activity_sum(asg);
                    if cutoff < value.min(c.rank_old as f64) {
                        perm.push(OrderedProxy::new(i, value));
                    }
                }
                ReductionType::LBDonADD(_) => {
                    perm.push(OrderedProxy::new(i, c.lbd()));
                }
                ReductionType::LBDonALL(cutoff, _) => {
                    let value = c.rank.min(c.rank_old);
                    if cutoff < value {
                        perm.push(OrderedProxy::new(i, value as f64));
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
        for i in perm.iter().skip(keep) {
            self.remove_clause(ClauseId::from(i.to()));
        }
    }
    fn reset(&mut self) {
        debug_assert!(1 < self.clause.len());
        for (i, cr) in &mut self.clause.iter_mut().enumerate().skip(1) {
            let rcc = cr.get();
            let c = rcc.borrow_mut();
            if c.is(FlagClause::LEARNT)
                && !c.is_dead()
                && (self.co_lbd_bound as usize) < c.lits.len()
            {
                let f = remove_clause_fn(
                    &mut self.certification_store,
                    &mut self.binary_link,
                    &mut self.watch_cache,
                    &mut self.num_bi_clause,
                    &mut self.num_clause,
                    &mut self.num_learnt,
                    ClauseId::from(i),
                    cr,
                );
                self.freelist.push(f);
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
    fn validate(&self, model: &[Option<bool>], strict: bool) -> Option<ClauseId> {
        for (i, cr) in self.clause.iter().enumerate().skip(1) {
            let rcc = cr.get();
            let c = rcc.borrow();
            if c.is_dead() || (strict && c.is(FlagClause::LEARNT)) {
                continue;
            }
            match c.evaluate(model) {
                Some(false) => return Some(ClauseId::from(i)),
                None if strict => return Some(ClauseId::from(i)),
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
        let mut temp = vec![false; asg.derefer(crate::assign::property::Tusize::NumVar)];
        // self.lbd_temp[0] += 1;
        // let key = self.lbd_temp[0];
        for l in &vec[1..] {
            // self.lbd_temp[l.vi() as usize] = key;
            temp[l.vi() as usize] = true;
        }
        let l0 = vec[0];
        let mut sat = false;
        for (_, cid) in self.binary_link.connect_with(l0).iter() {
            // let c = &self.clause[NonZeroU32::get(cid.ordinal) as usize];
            let rcc = &self[cid];
            let c = rcc.borrow();
            debug_assert!(c[0] == l0 || c[1] == l0);
            let other = c[(c[0] == l0) as usize];
            drop(c);
            let vi = other.vi();
            if temp[vi] && asg.assigned(other) == Some(true) {
                sat = true;
                temp[vi] = false;
            }
            // if self.lbd_temp[vi] == key && asg.assigned(other) == Some(true) {
            //     num_sat += 1;
            //     self.lbd_temp[vi] = key - 1;
            // }
        }
        if sat {
            temp[l0.vi()] = true;
            vec.retain(|l| temp[l.vi()]);
            // self.lbd_temp[l0.vi()] = key;
            // vec.retain(|l| self.lbd_temp[l.vi()] == key);
        }
    }
    fn complete_bi_clauses(&mut self, asg: &mut impl AssignIF) {
        while let Some(lit) = self.bi_clause_completion_queue.pop() {
            self.complete_bi_clauses_with(asg, lit);
        }
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
        let nc = self
            .iter()
            .skip(1)
            .filter(|rcc| {
                let c = rcc.borrow();
                !c.is_dead()
            })
            .count();
        buf.write_all(format!("p cnf {} {}\n", nv, nc + na).as_bytes())
            .unwrap();
        for rcc in self.iter().skip(1) {
            let c = rcc.borrow();
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
    fn link_to_cid(&self, l0: Lit, l1: Lit) -> Option<&ClauseId> {
        self.binary_link.search(l0, l1)
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
fn remove_clause_fn(
    certification_store: &mut CertificationStore,
    binary_link: &mut BinaryLinkDB,
    watcher: &mut [WatchCache],
    num_bi_clause: &mut usize,
    num_clause: &mut usize,
    num_learnt: &mut usize,
    cid: ClauseId,
    cr: &ClauseRef,
) -> ClauseId {
    let rcc = cr.get();
    let mut c = rcc.borrow_mut();
    debug_assert!(!c.is_dead());
    let l0 = c.lits[0];
    let l1 = c.lits[1];
    if c.len() == 2 {
        binary_link
            .remove(l0, l1)
            .expect("Eror (remove_clause_fn#01)");
        *num_bi_clause -= 1;
    } else {
        watcher[usize::from(!l0)].remove_watch(&cid); // .expect("db1076");
        watcher[usize::from(!l1)].remove_watch(&cid); // .expect("db1077");
    }
    if c.is(FlagClause::LEARNT) {
        *num_learnt -= 1;
    }
    *num_clause -= 1;
    certification_store.delete_clause(&c.lits);
    // c.lits.clear();
    c.turn_on(FlagClause::DEAD);
    cid
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

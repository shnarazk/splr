use {
    super::{
        binary::{BinaryLinkIF, BinaryLinkList},
        cref::ClauseRef,
        ema::ProgressLBD,
        property,
        watch_cache::*,
        BinaryLinkDB, CertificationStore, Clause, ClauseDB, ClauseDBIF, ReductionType, RefClause,
    },
    crate::{assign::AssignIF, types::*},
    std::collections::{hash_set::Iter, HashSet},
};

#[cfg(not(feature = "no_IO"))]
use std::{fs::File, io::Write, path::Path};

impl Default for ClauseDB {
    fn default() -> ClauseDB {
        ClauseDB {
            next_clause_id: 1, // id 0 is used by lifted clauses from a literal
            clause: HashSet::new(),
            binary_link: BinaryLinkDB::default(),
            watch_cache: Vec::new(),
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
            eliminated_permanent: Vec::new(),
        }
    }
}

// impl Index<ClauseRef> for ClauseDB {
//     type Output = ClauseRef;
//     #[inline]
//     fn index(&self, cid: ClauseRef) -> &ClauseRef {
//         self.clause[cid]
//         let i = NonZeroU32::get(cid.ordinal) as usize;
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.clause.get_unchecked(i)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self.clause[i]
//     }
// }

// impl IndexMut<ClauseRef> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, cid: ClauseRef) -> &mut Clause {
//         let i = NonZeroU32::get(cid.ordinal) as usize;
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.clause.get_unchecked_mut(i)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self.clause[i]
//     }
// }

// impl Index<&ClauseRef> for ClauseDB {
//     type Output = Clause;
//     #[inline]
//     fn index(&self, cid: &ClauseRef) -> &Clause {
//         let i = NonZeroU32::get(cid.ordinal) as usize;
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.clause.get_unchecked(i)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self.clause[i]
//     }
// }

// impl IndexMut<&ClauseRef> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, cid: &ClauseRef) -> &mut Clause {
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
//     type Output = [Clause];
//     #[inline]
//     fn index(&self, r: Range<usize>) -> &[Clause] {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.clause.get_unchecked(r)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self.clause[r]
//     }
// }

// impl Index<RangeFrom<usize>> for ClauseDB {
//     type Output = [Clause];
//     #[inline]
//     fn index(&self, r: RangeFrom<usize>) -> &[Clause] {
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
        // let nc = cnf.num_of_clauses;
        // let mut clause = Vec::with_capacity(1 + nc);
        // clause.push(Clause::default());
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        for _ in 0..2 * (nv + 1) {
            watcher.push(WatchCache::new());
        }
        ClauseDB {
            clause: HashSet::new(),
            binary_link: BinaryLinkDB::instantiate(config, cnf),
            watch_cache: watcher,
            certification_store: CertificationStore::instantiate(config, cnf),
            soft_limit: config.c_cls_lim,
            lbd: ProgressLBD::instantiate(config, cnf),

            #[cfg(feature = "clause_rewarding")]
            activity_decay: config.crw_dcy_rat,
            #[cfg(feature = "clause_rewarding")]
            activity_anti_decay: 1.0 - config.crw_dcy_rat,

            lbd_temp: vec![0; nv + 1],
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
                self.lbd_temp.push(0);
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
    fn iter(&self) -> Iter<'_, ClauseRef> {
        self.clause.iter()
    }
    #[inline]
    fn binary_links(&self, l: Lit) -> &BinaryLinkList {
        self.binary_link.connect_with(l)
    }
    // watch_cache_IF
    fn fetch_watch_cache_entry(&self, lit: Lit, wix: WatchCacheProxy) -> &(ClauseRef, Lit) {
        &self.watch_cache[lit][wix]
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
    fn swap_watch(&mut self, c: &mut Clause) {
        // let rcc = cr.get();
        // let mut c = rcc.borrow_mut();
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
            if let Some(cr) = self.link_to_cid(vec[0], vec[1]) {
                let cref = cr.clone();
                self.num_reregistration += 1;
                return RefClause::RegisteredClause(cref);
            }
        }
        self.certification_store.add_clause(vec);
        let mut c = Clause {
            flags: FlagClause::empty(),
            ..Clause::default()
        };
        std::mem::swap(&mut c.lits, vec);

        let ClauseDB {
            #[cfg(feature = "bi_clause_completion")]
            ref mut bi_clause_completion_queue,
            // ref mut clause,
            ref mut lbd_temp,
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
            c.update_lbd(asg, lbd_temp);
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
        let cr = ClauseRef::new(self.next_clause_id, c);
        self.next_clause_id += 1;
        self.clause.insert(cr.clone());
        if len2 {
            *num_bi_clause += 1;
            binary_link.add(l0, l1, cr.clone());
        } else {
            watch_cache[!l0].insert_watch(cr.clone(), l1);
            watch_cache[!l1].insert_watch(cr.clone(), l0);
        }
        RefClause::Clause(cr)
    }
    fn new_clause_sandbox(&mut self, asg: &mut impl AssignIF, vec: &mut Vec<Lit>) -> RefClause {
        debug_assert!(1 < vec.len());
        if vec.len() == 2 {
            if let Some(cr) = self.link_to_cid(vec[0], vec[1]) {
                return RefClause::RegisteredClause(cr.clone());
            }
        }
        let mut c = Clause {
            flags: FlagClause::empty(),
            ..Clause::default()
        };
        std::mem::swap(&mut c.lits, vec);

        let ClauseDB {
            // ref mut clause,
            ref mut lbd_temp,
            ref mut binary_link,
            #[cfg(feature = "clause_rewarding")]
            ref tick,
            ref mut watch_cache,
            ..
        } = self;

        #[cfg(feature = "clause_rewarding")]
        {
            c.timestamp = *tick;
        }

        let len2 = c.lits.len() == 2;
        if len2 {
            c.rank = 1;
            c.rank_old = 1;
        } else {
            c.update_lbd(asg, lbd_temp);
            c.rank_old = c.rank;
            c.turn_on(FlagClause::LEARNT);
        }
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        let cr = ClauseRef::new(self.next_clause_id, c);
        self.next_clause_id += 1;
        self.clause.insert(cr.clone());
        if len2 {
            binary_link.add(l0, l1, cr.clone());
        } else {
            watch_cache[!l0].insert_watch(cr.clone(), l1);
            watch_cache[!l1].insert_watch(cr.clone(), l0);
        }
        RefClause::Clause(cr)
    }
    /// ## Warning
    /// this function is the only function that makes dead clauses
    fn remove_clause(&mut self, cr: ClauseRef) {
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
        // if !self.clause[NonZeroU32::get(cr.ordinal) as usize].is_dead() {
        // }
        let cr1 = cr.clone();
        let rcc = cr1.get();
        let c = rcc.borrow();
        debug_assert!(!c.is_dead());
        debug_assert!(1 < c.lits.len());
        drop(c);
        remove_clause_fn(
            &mut self.clause,
            &mut self.certification_store,
            &mut self.binary_link,
            &mut self.watch_cache,
            &mut self.num_bi_clause,
            &mut self.num_clause,
            &mut self.num_learnt,
            cr,
        );
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
    }
    fn remove_clause_sandbox(&mut self, cr: ClauseRef) {
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
        // let c = &mut cr.get_mut();
        let cr1 = cr.clone();
        let rcc = cr1.get();
        let c = rcc.borrow();
        debug_assert!(!c.is_dead());
        debug_assert!(1 < c.lits.len());
        let mut store = CertificationStore::default();
        let mut dummy1 = 1;
        let mut dummy2 = 1;
        let mut dummy3 = 1;
        drop(c);
        remove_clause_fn(
            &mut self.clause,
            &mut store,
            &mut self.binary_link,
            &mut self.watch_cache,
            &mut dummy1,
            &mut dummy2,
            &mut dummy3,
            cr,
        );
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
    fn transform_by_elimination(&mut self, cr: ClauseRef, p: Lit) -> RefClause {
        //
        //## Clause transform rules
        //
        // There are four cases:
        // 1. a bi-clause becomes a unit clause.                   [Case:2-1]
        // 2. a normal clause is merged to a registered bi-clause. [Case:3-0]
        // 3. a normal clause becomes a new bi-clause.             [Case:3-2]
        // 4. a normal clause becomes a shorter normal clause.     [Case:3-3]
        //

        // self.watches(cr, "before strengthen_by_elimination");
        // let mut writer = cr.clone();
        // let c = writer.get_mut();
        // let rcc = &mut cr.get_mut();
        let rcc = &mut cr.get();
        let mut c = rcc.borrow_mut();
        debug_assert!(!c.is_dead());
        debug_assert!(1 < c.len());
        let ClauseDB {
            // ref mut clause,
            ref mut binary_link,
            ref mut watch_cache,
            ref mut certification_store,
            ref mut num_bi_clause,
            ..
        } = self;
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
        let mut new_lits: Vec<Lit> = c
            .lits
            .iter()
            .filter(|&l| *l != p)
            .copied()
            .collect::<Vec<Lit>>();
        if new_lits.len() == 2 {
            if let Some(reg) = binary_link.search(new_lits[0], new_lits[1]) {
                //
                //## Case:3-0
                //
                return RefClause::RegisteredClause(reg.clone());
            }
            //
            //## Case:3-2
            //
            let l0 = c.lits[0];
            let l1 = c.lits[1];
            std::mem::swap(&mut c.lits, &mut new_lits);
            watch_cache[!l0].remove_watch(&cr);
            watch_cache[!l1].remove_watch(&cr);
            binary_link.add(c.lits[0], c.lits[1], cr.clone());
            *num_bi_clause += 1;
            // self.watches(cr, "after strengthen_by_elimination case:3-2");
        } else {
            let old_l0 = c.lits[0];
            let old_l1 = c.lits[1];
            std::mem::swap(&mut c.lits, &mut new_lits);
            let l0 = c.lits[0];
            let l1 = c.lits[1];
            //
            //## Case:3-3
            //

            // Here we assumed that there's no eliminated var in clause and *watch cache*.
            // Fortunately the current implementation purges all eliminated vars fully.
            if p == old_l0 {
                watch_cache[!p].remove_watch(&cr);
                if old_l1 == l0 {
                    debug_assert!(watch_cache[!l1].iter().all(|e| e.0 != cr));
                    watch_cache[!l1].insert_watch(cr.clone(), l0);

                    #[cfg(feature = "maintain_watch_cache")]
                    {
                        watch_cache[!l0].update_watch(cr, l1);
                    }
                } else if old_l1 == l1 {
                    debug_assert!(watch_cache[!l0].iter().all(|e| e.0 != cr));
                    watch_cache[!l0].insert_watch(cr.clone(), l1);

                    #[cfg(feature = "maintain_watch_cache")]
                    {
                        watch_cache[!l1].update_watch(cr, l0);
                    }
                } else {
                    unreachable!("transform_by_elimination");
                }
            } else if p == old_l1 {
                watch_cache[!p].remove_watch(&cr);
                if old_l0 == l0 {
                    debug_assert!(watch_cache[!l1].iter().all(|e| e.0 != cr));
                    watch_cache[!l1].insert_watch(cr.clone(), l0);

                    #[cfg(feature = "maintain_watch_cache")]
                    {
                        watch_cache[!l0].update_watch(cr, l1);
                    }
                } else if old_l0 == l1 {
                    debug_assert!(watch_cache[!l0].iter().all(|e| e.0 != cr));
                    watch_cache[!l0].insert_watch(cr.clone(), l1);

                    #[cfg(feature = "maintain_watch_cache")]
                    {
                        watch_cache[!l1].update_watch(cr, l0);
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
                    .any(|wc| wc.0 == cr && wc.1 == c.lits[1]));
                debug_assert!(watch_cache[!c.lits[1]]
                    .iter()
                    .any(|wc| wc.0 == cr && wc.1 == c.lits[0]));
            }

            // self.watches(cr, "after strengthen_by_elimination case:3-3");
        }
        if certification_store.is_active() {
            certification_store.add_clause(&c.lits);
            certification_store.delete_clause(&new_lits);
        }
        RefClause::Clause(cr.clone())
    }
    // Not in use so far
    fn transform_by_replacement(&mut self, cr: ClauseRef, new_lits: &mut Vec<Lit>) -> RefClause {
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
            // clause,
            binary_link,
            watch_cache,
            certification_store,
            ..
        } = self;
        // let mut write = cr.clone();
        // let c = write.get_mut();
        let rcc = &mut cr.get();
        let mut c = rcc.borrow_mut();
        debug_assert!(!c.is_dead());
        debug_assert!(new_lits.len() < c.len());
        if new_lits.len() == 2 {
            if let Some(dr) = binary_link.search(new_lits[0], new_lits[1]) {
                //
                //## Case:0
                //
                if certification_store.is_active() {
                    certification_store.delete_clause(new_lits);
                }
                return RefClause::RegisteredClause(dr.clone());
            }
            //
            //## Case:2
            //
            let old_l0 = c.lit0();
            let old_l1 = c.lit0();
            std::mem::swap(&mut c.lits, new_lits);
            let l0 = c.lit0();
            let l1 = c.lit0();
            watch_cache[!old_l0].remove_watch(&cr);
            watch_cache[!old_l1].remove_watch(&cr);
            binary_link.add(l0, l1, cr.clone());

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
                watch_cache[!old_l1].remove_watch(&cr);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cr));
                watch_cache[!l0].update_watch(cr.clone(), l1);
                // assert!(watch_cache[!l1].iter().all(|e| e.0 != cr));
                watch_cache[!l1].insert_watch(cr.clone(), l0);
            } else if l0 == old_l1 {
                watch_cache[!old_l0].remove_watch(&cr);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cr));
                watch_cache[!l0].update_watch(cr.clone(), l1);
                // assert!(watch_cache[!l1].iter().all(|e| e.0 != cr));
                watch_cache[!l1].insert_watch(cr.clone(), l0);
            } else if l1 == old_l0 {
                watch_cache[!old_l1].remove_watch(&cr);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cr));
                watch_cache[!l0].insert_watch(cr.clone(), l1);
                watch_cache[!l1].update_watch(cr.clone(), l0);
            } else if l1 == old_l1 {
                watch_cache[!old_l0].remove_watch(&cr);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cr));
                watch_cache[!l0].insert_watch(cr.clone(), l1);
                watch_cache[!l1].update_watch(cr.clone(), l0);
            } else {
                watch_cache[!old_l0].remove_watch(&cr);
                watch_cache[!old_l1].remove_watch(&cr);
                // assert!(watch_cache[!l0].iter().all(|e| e.0 != cr));
                watch_cache[!l0].insert_watch(cr.clone(), l1);
                // assert!(watch_cache[!l1].iter().all(|e| e.0 != cr));
                watch_cache[!l1].insert_watch(cr.clone(), l0);
            }

            // maintain_watch_literal \\ assert!(watch_cache[!c.lits[0]].iter().any(|wc| wc.0 == cr && wc.1 == c.lits[1]));
            // maintain_watch_literal \\ assert!(watch_cache[!c.lits[1]].iter().any(|wc| wc.0 == cr && wc.1 == c.lits[0]));

            if certification_store.is_active() {
                certification_store.add_clause(new_lits);
                certification_store.delete_clause(&c.lits);
            }
        }
        RefClause::Clause(cr.clone())
    }
    // only used in `propagate_at_root_level`
    fn transform_by_simplification(&mut self, asg: &mut impl AssignIF, cr: ClauseRef) -> RefClause {
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
        // let mut writer = cr.clone();
        // let c = writer.get_mut();
        let rcc = &mut cr.get();
        let mut c = rcc.borrow_mut();
        debug_assert!(!c.is_dead());
        // firstly sweep without consuming extra memory
        let mut need_to_shrink = false;
        for l in c.iter() {
            debug_assert!(!asg.var(l.vi()).is(FlagVar::ELIMINATED));
            match asg.assigned(*l) {
                Some(true) => {
                    drop(c);
                    self.remove_clause(cr.clone());
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
            return RefClause::Clause(cr.clone());
        }
        let ClauseDB {
            // clause,
            binary_link,
            watch_cache,
            certification_store,
            ..
        } = self;
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
                if let Some(br) = binary_link.search(l0, l1) {
                    //
                    //## Case:3-0
                    //
                    let br2 = br.clone();
                    drop(c);
                    self.remove_clause(cr.clone());
                    return RefClause::RegisteredClause(br2);
                }
                //
                //## Case:3-2
                //
                watch_cache[!c.lits[0]].remove_watch(&cr);
                watch_cache[!c.lits[1]].remove_watch(&cr);
                binary_link.add(l0, l1, cr.clone());
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
                RefClause::Clause(cr.clone())
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
                        watch_cache[!l0].update_watch(cr, l1);
                        watch_cache[!l1].update_watch(cr, l0);
                    }
                } else if old_l0 == l0 {
                    // assert_ne!(old_l1, l1);
                    watch_cache[!old_l1].remove_watch(&cr);
                    watch_cache[!l0].update_watch(cr.clone(), l1);
                    // assert!(watch_cache[!l1].iter().all(|e| e.0 != cr));
                    watch_cache[!l1].insert_watch(cr.clone(), l0);
                } else if old_l0 == l1 {
                    // assert_ne!(old_l1, l0);
                    watch_cache[!old_l1].remove_watch(&cr);
                    // assert!(watch_cache[!l0].iter().all(|e| e.0 != cr));
                    watch_cache[!l0].insert_watch(cr.clone(), l1);
                    watch_cache[!l1].update_watch(cr.clone(), l0);
                } else if old_l1 == l0 {
                    // assert_ne!(old_l0, l1);
                    watch_cache[!old_l0].remove_watch(&cr);
                    watch_cache[!l0].update_watch(cr.clone(), l1);
                    watch_cache[!l1].insert_watch(cr.clone(), l0);
                } else if old_l1 == l1 {
                    // assert_ne!(old_l0, l0);
                    watch_cache[!old_l0].remove_watch(&cr);
                    watch_cache[!l0].insert_watch(cr.clone(), l1);
                    watch_cache[!l1].update_watch(cr.clone(), l0);
                } else {
                    watch_cache[!old_l0].remove_watch(&cr);
                    watch_cache[!old_l1].remove_watch(&cr);
                    // assert!(watch_cache[!l0].iter().all(|e| e.0 != cr));
                    watch_cache[!l0].insert_watch(cr.clone(), l1);
                    // assert!(watch_cache[!l1].iter().all(|e| e.0 != cr));
                    watch_cache[!l1].insert_watch(cr.clone(), l0);
                }

                // maintain_watch_literal \\ assert!(watch_cache[!c.lits[0]].iter().any(|wc| wc.0 == cr && wc.1 == c.lits[1]));
                // maintain_watch_literal \\ assert!(watch_cache[!c.lits[1]].iter().any(|wc| wc.0 == cr && wc.1 == c.lits[0]));

                if certification_store.is_active() {
                    certification_store.add_clause(&c.lits);
                    certification_store.delete_clause(&new_lits);
                }
                RefClause::Clause(cr.clone())
            }
        }
    }
    // used in `propagate`, `propagate_sandbox`, and `handle_conflict` for chronoBT
    fn transform_by_updating_watch(
        &mut self,
        cr: ClauseRef,
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

        debug_assert!(old < 2);
        debug_assert!(1 < new);
        let ClauseDB {
            // ref mut clause,
            ref mut watch_cache,
            ..
        } = self;
        // let mut writer = cr.clone();
        // let c = writer.get_mut();
        let rcc = &mut cr.get();
        let mut c = rcc.borrow_mut();
        debug_assert!(!c.is_dead());
        let other = (old == 0) as usize;
        if removed {
            debug_assert!(watch_cache[!c.lits[old]].get_watch(&cr).is_none());
        } else {
            //## Step:1
            watch_cache[!c.lits[old]].remove_watch(&cr);
        }
        //## Step:2
        // assert!(watch_cache[!c.lits[new]].iter().all(|e| e.0 != cr));
        watch_cache[!c.lits[new]].insert_watch(cr.clone(), c.lits[other]);

        #[cfg(feature = "maintain_watch_cache")]
        {
            //## Step:3
            watch_cache[!c.lits[other]].update_watch(cr, c.lits[new]);
        }

        c.lits.swap(old, new);

        // maintain_watch_literal \\ assert!(watch_cache[!c.lits[0]].iter().any(|wc| wc.0 == cr && wc.1 == c.lits[1]));
        // maintain_watch_literal \\ assert!(watch_cache[!c.lits[1]].iter().any(|wc| wc.0 == cr && wc.1 == c.lits[0]));
    }
    fn update_at_analysis(&mut self, asg: &impl AssignIF, cr: ClauseRef) -> bool {
        // let mut writer = cr.clone();
        // let c = writer.get_mut();
        let rcc = &mut cr.get();
        let mut c = rcc.borrow_mut();
        // Updating LBD at every analysis seems redundant.
        // But it's crucial. Don't remove the below.
        let rank = c.update_lbd(asg, &mut self.lbd_temp);
        let learnt = c.is(FlagClause::LEARNT);
        if learnt {
            #[cfg(feature = "just_used")]
            c.turn_on(FlagClause::USED);
            #[cfg(feature = "clause_rewading")]
            self.reward_at_analysis(cr);
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

        let mut perm: Vec<OrderedProxy<ClauseRef>> = Vec::with_capacity(clause.len());
        let mut alives = 0;
        for cr in clause.iter() {
            // let mut writer = cr.clone();
            // let c = writer.get_mut();
            let rcc = &mut cr.get();
            let mut c = rcc.borrow_mut();
            c.update_lbd(asg, lbd_temp);

            #[cfg(feature = "clause_rewarding")]
            c.update_activity(*tick, *activity_decay, 0.0);

            // There's no clause stored in `reason` because the decision level is 'zero.'
            debug_assert_ne!(
                asg.reason(c.lit0().vi()),
                &AssignReason::Implication(cr.clone()),
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
                    perm.push(OrderedProxy::new(cr.clone(), c.reverse_activity_sum(asg)));
                }
                ReductionType::RASonALL(cutoff, _) => {
                    let value = c.reverse_activity_sum(asg);
                    if cutoff < value.min(c.rank_old as f64) {
                        perm.push(OrderedProxy::new(cr.clone(), value));
                    }
                }
                ReductionType::LBDonADD(_) => {
                    perm.push(OrderedProxy::new(cr.clone(), c.lbd()));
                }
                ReductionType::LBDonALL(cutoff, _) => {
                    let value = c.rank.min(c.rank_old);
                    if cutoff < value {
                        perm.push(OrderedProxy::new(cr.clone(), value as f64));
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
        for op in perm.iter().skip(keep) {
            self.remove_clause(op.to().clone());
        }
    }
    fn reset(&mut self) {
        debug_assert!(1 < self.clause.len());
        let pool = self.clause.clone();
        for cr in pool.iter() {
            // let c = cr.get();
            let rcc = &mut cr.get();
            let c = rcc.borrow_mut();
            if c.is(FlagClause::LEARNT)
                && !c.is_dead()
                && (self.co_lbd_bound as usize) < c.lits.len()
            {
                drop(c);
                remove_clause_fn(
                    &mut self.clause,
                    &mut self.certification_store,
                    &mut self.binary_link,
                    &mut self.watch_cache,
                    &mut self.num_bi_clause,
                    &mut self.num_clause,
                    &mut self.num_learnt,
                    cr.clone(),
                );
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
    fn validate(&self, model: &[Option<bool>], strict: bool) -> Option<ClauseRef> {
        for cr in self.clause.iter() {
            // let c = cr.get();
            let rcc = &mut cr.get();
            let c = rcc.borrow_mut();
            if c.is_dead() || (strict && c.is(FlagClause::LEARNT)) {
                continue;
            }
            match c.evaluate(model) {
                Some(false) => return Some(cr.clone()),
                None if strict => return Some(cr.clone()),
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
        for (_, cr) in self.binary_link.connect_with(l0).iter() {
            // let c = cr.get();
            let rcc = &mut cr.get();
            let c = rcc.borrow_mut();
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
    #[cfg(feature = "incremental_solver")]
    fn make_permanent_immortal(&mut self, cid: ClauseRef) {
        self.eliminated_permanent.push(
            self.clause[NonZeroU32::get(cid.ordinal) as usize]
                .lits
                .clone(),
        );
    }
    #[cfg(feature = "boundary_check")]
    fn watch_cache_contains(&self, lit: Lit, cid: ClauseRef) -> bool {
        self.watch_cache[lit].iter().any(|w| w.0 == cid)
    }
    #[cfg(feature = "boundary_check")]
    fn watch_caches(&self, cid: ClauseRef, mes: &str) -> (Vec<Lit>, Vec<Lit>) {
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
    fn is_garbage_collected(&mut self, cid: ClauseRef) -> Option<bool> {
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
            .filter(|cr| {
                let rcc = &mut cr.get();
                let c = rcc.borrow_mut();
                !c.is_dead()
            })
            .count();
        buf.write_all(format!("p cnf {} {}\n", nv, nc + na).as_bytes())
            .unwrap();
        for cr in self.iter() {
            // let c = cr.get();
            let rcc = &mut cr.get();
            let c = rcc.borrow_mut();
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
    fn link_to_cid(&self, l0: Lit, l1: Lit) -> Option<&ClauseRef> {
        self.binary_link.search(l0, l1)
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
fn remove_clause_fn(
    clause_pool: &mut HashSet<ClauseRef>,
    certification_store: &mut CertificationStore,
    binary_link: &mut BinaryLinkDB,
    watcher: &mut [WatchCache],
    num_bi_clause: &mut usize,
    num_clause: &mut usize,
    num_learnt: &mut usize,
    cr: ClauseRef,
) {
    // let c = cr.get();
    let rcc = &mut cr.get();
    let c = rcc.borrow_mut();
    debug_assert!(!c.is_dead());
    let l0 = c.lits[0];
    let l1 = c.lits[1];
    if c.len() == 2 {
        binary_link
            .remove(l0, l1)
            .expect("Eror (remove_clause_fn#01)");
        *num_bi_clause -= 1;
    } else {
        watcher[usize::from(!l0)].remove_watch(&cr); // .expect("db1076");
        watcher[usize::from(!l1)].remove_watch(&cr); // .expect("db1077");
    }
    if c.is(FlagClause::LEARNT) {
        *num_learnt -= 1;
    }
    certification_store.delete_clause(&c.lits);
    drop(c);
    if clause_pool.remove(&cr) {
        *num_clause -= 1;
    };
    // c.lits.clear();
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

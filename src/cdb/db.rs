use {
    super::{
        property, watch_cache::*, CertificationStore, Clause, ClauseDB, ClauseDBIF, ClauseId,
        RefClause,
    },
    crate::{assign::AssignIF, solver::SolverEvent, types::*},
    std::{
        collections::HashMap,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::{Iter, IterMut},
    },
};

impl Default for ClauseDB {
    fn default() -> ClauseDB {
        ClauseDB {
            clause: Vec::new(),
            bi_clause: Vec::new(),
            watch_cache: Vec::new(),
            freelist: Vec::new(),
            certification_store: CertificationStore::default(),
            soft_limit: 0, // 248_000_000
            use_chan_seok: false,
            co_lbd_bound: 4,
            bi_clause_completion_queue: Vec::new(),
            num_bi_clause_completion: 0,
            // lbd_frozen_clause: 30,
            ordinal: 0,
            activity_decay: 0.99,
            activity_anti_decay: 0.01,
            activity_ema: Ema::new(1000),
            lbd_temp: Vec::new(),
            num_lbd_update: 0,
            inc_step: 300,
            extra_inc: 1000,
            first_reduction: 1000,
            next_reduction: 1000,
            reducible: true,
            reduction_coeff: 1,
            num_clause: 0,
            num_bi_clause: 0,
            num_bi_learnt: 0,
            num_lbd2: 0,
            num_learnt: 0,
            num_reduction: 0,
            num_reregistration: 0,
            lbd_of_dp_ema: Ema::new(100_000),
            eliminated_permanent: Vec::new(),
        }
    }
}

impl Index<ClauseId> for ClauseDB {
    type Output = Clause;
    #[inline]
    fn index(&self, cid: ClauseId) -> &Clause {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked(cid.ordinal as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.clause[cid.ordinal as usize]
    }
}

impl IndexMut<ClauseId> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, cid: ClauseId) -> &mut Clause {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked_mut(cid.ordinal as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.clause[cid.ordinal as usize]
    }
}

impl Index<&ClauseId> for ClauseDB {
    type Output = Clause;
    #[inline]
    fn index(&self, cid: &ClauseId) -> &Clause {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked(cid.ordinal as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.clause[cid.ordinal as usize]
    }
}

impl IndexMut<&ClauseId> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, cid: &ClauseId) -> &mut Clause {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked_mut(cid.ordinal as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.clause[cid.ordinal as usize]
    }
}

impl Index<Range<usize>> for ClauseDB {
    type Output = [Clause];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Clause] {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.clause[r]
    }
}

impl Index<RangeFrom<usize>> for ClauseDB {
    type Output = [Clause];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Clause] {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.clause[r]
    }
}

impl IndexMut<Range<usize>> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Clause] {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked_mut(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.clause[r]
    }
}

impl IndexMut<RangeFrom<usize>> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Clause] {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.clause.get_unchecked_mut(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.clause[r]
    }
}

impl ActivityIF<ClauseId> for ClauseDB {
    fn activity(&mut self, cid: ClauseId) -> f64 {
        let t = self.ordinal;
        self.clause[cid.ordinal as usize].update_activity(
            t,
            self.activity_decay,
            self.activity_anti_decay,
        )
    }
    fn average_activity(&self) -> f64 {
        self.activity_ema.get()
    }
    fn set_activity(&mut self, cid: ClauseId, val: f64) {
        self[cid].reward = val;
    }
    fn reward_at_analysis(&mut self, cid: ClauseId) {
        // Note: vivifier has its own conflict analyzer, which never call reward functions.
        let t = self.ordinal;
        let r = self.clause[cid.ordinal as usize].update_activity(
            t,
            self.activity_decay,
            self.activity_anti_decay,
        );
        self.activity_ema.update(r);
    }
    fn update_rewards(&mut self) {
        self.ordinal += 1;
    }
}

impl Instantiate for ClauseDB {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> ClauseDB {
        let nv = cnf.num_of_variables;
        let nc = cnf.num_of_clauses;
        let mut clause = Vec::with_capacity(1 + nc);
        clause.push(Clause::default());
        let mut bi_clause = Vec::with_capacity(2 * (nv + 1));
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        for _ in 0..2 * (nv + 1) {
            bi_clause.push(BiClause::new());
            watcher.push(WatchCache::new());
        }
        ClauseDB {
            clause,
            bi_clause,
            watch_cache: watcher,
            certification_store: CertificationStore::instantiate(config, cnf),
            soft_limit: config.c_cls_lim,
            activity_decay: config.crw_dcy_rat,
            activity_anti_decay: 1.0 - config.crw_dcy_rat,
            lbd_temp: vec![0; nv + 1],
            ..ClauseDB::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        #[allow(clippy::single_match)]
        match e {
            #[cfg(feature = "strategy_adaptation")]
            SolverEvent::Adapt(strategy, num_conflict) => {
                // # PRECONDITION
                // decision level must be 0 if `state.strategy.1` == `state[Stat::Conflict]`
                match strategy {
                    (_, n) if n != num_conflict => (),
                    (crate::state::SearchStrategy::Initial, _) => (),
                    (crate::state::SearchStrategy::Generic, _) => (),
                    (crate::state::SearchStrategy::LowDecisions, _) => {
                        self.co_lbd_bound = 4;
                        self.reduction_coeff =
                            (num_conflict as f64 / self.next_reduction as f64 + 1.0) as usize;
                        self.first_reduction = 2000;
                        self.use_chan_seok = true;
                        self.inc_step = 0;
                        self.next_reduction = 2000;
                        // This call requires 'decision level == 0'.
                        self.make_permanent(true);
                    }
                    (crate::state::SearchStrategy::HighSuccessive, _) => {
                        self.co_lbd_bound = 3;
                        self.first_reduction = 30000;
                        self.use_chan_seok = true;
                        // This call requires 'decision level == 0'.
                        self.make_permanent(false);
                    }
                    (crate::state::SearchStrategy::LowSuccessive, _) => (),
                    (crate::state::SearchStrategy::ManyGlues, _) => (),
                }
            }
            SolverEvent::NewVar => {
                // for negated literal
                self.bi_clause.push(HashMap::new());
                self.watch_cache.push(WatchCache::new());
                // for positive literal
                self.bi_clause.push(HashMap::new());
                self.watch_cache.push(WatchCache::new());
                self.lbd_temp.push(0);
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
    fn iter(&self) -> Iter<'_, Clause> {
        self.clause.iter()
    }
    fn iter_mut(&mut self) -> IterMut<'_, Clause> {
        self.clause.iter_mut()
    }
    #[inline]
    fn bi_clause_map(&self, l: Lit) -> &HashMap<Lit, ClauseId> {
        &self.bi_clause[l]
    }
    #[inline]
    fn detach_watch_cache(&mut self, l: Lit) -> WatchCache {
        let mut empty = WatchCache::new();
        std::mem::swap(&mut self.watch_cache[l], &mut empty);
        empty
    }
    fn reregister_watch_cache(&mut self, p: Lit, target: Option<(ClauseId, Lit)>) -> bool {
        if let Some((cid, lit)) = target {
            self.watch_cache[p].insert_watch(cid, lit);
            return true;
        }
        false
    }
    fn merge_watch_cache(&mut self, p: Lit, wc: WatchCache) {
        self.watch_cache[p].append_watch(wc);
    }
    fn swap_watch(&mut self, cid: ClauseId) {
        self[cid].lits.swap(0, 1);
    }
    fn new_clause<A>(&mut self, asg: &mut A, vec: &mut Vec<Lit>, mut learnt: bool) -> RefClause
    where
        A: AssignIF,
    {
        debug_assert!(vec.iter().all(|l| !vec.contains(&!*l)), "{:?}", vec,);
        assert!(1 < vec.len());
        if vec.len() == 2 {
            if let Some(cid) = self.has_bi_clause(vec[0], vec[1]) {
                self.num_reregistration += 1;
                return RefClause::RegisteredClause(cid);
            }
        }
        self.certification_store.push_add(vec);
        let cid;
        if let Some(cid_used) = self.freelist.pop() {
            cid = cid_used;
            let c = &mut self[cid];
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
            c.flags = Flag::empty();
            debug_assert!(c.lits.is_empty()); // c.lits.clear();
            std::mem::swap(&mut c.lits, vec);
            c.search_from = 2;
        } else {
            cid = ClauseId::from(self.clause.len());
            let mut c = Clause {
                flags: Flag::empty(),
                ..Clause::default()
            };
            std::mem::swap(&mut c.lits, vec);
            self.clause.push(c);
        };

        let ClauseDB {
            ref mut clause,
            ref mut lbd_temp,
            ref mut num_clause,
            ref mut num_bi_clause,
            ref mut num_bi_learnt,
            ref mut num_lbd2,
            ref mut num_learnt,
            ref mut bi_clause,
            ref ordinal,
            ref mut watch_cache,
            ..
        } = self;
        let c = &mut clause[cid.ordinal as usize];
        c.timestamp = *ordinal;
        let len2 = c.lits.len() == 2;
        if len2 {
            c.rank = 1;
        } else {
            c.update_lbd(asg, lbd_temp);
        }
        if learnt && len2 {
            *num_bi_learnt += 1;
        }
        if c.lits.len() <= 2 || (self.use_chan_seok && c.rank <= self.co_lbd_bound) {
            learnt = false;
        }
        if learnt {
            c.turn_on(Flag::LEARNT);

            if c.rank <= 2 {
                *num_lbd2 += 1;
            }
            *num_learnt += 1;
        }
        *num_clause += 1;
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        if len2 {
            // assert_eq!(c.lits.len(), 2);
            *num_bi_clause += 1;
            bi_clause[!l0].insert(l1, cid);
            bi_clause[!l1].insert(l0, cid);
        } else {
            // assert!(2 < c.lits.len());
            watch_cache[!l0].insert_watch(cid, l1);
            watch_cache[!l1].insert_watch(cid, l0);
        }
        RefClause::Clause(cid)
    }
    fn new_clause_sandbox<A>(&mut self, asg: &mut A, vec: &mut Vec<Lit>) -> RefClause
    where
        A: AssignIF,
    {
        assert!(1 < vec.len());
        let mut learnt: bool = true;
        if vec.len() == 2 {
            if let Some(cid) = self.has_bi_clause(vec[0], vec[1]) {
                return RefClause::RegisteredClause(cid);
            }
        }
        let cid;
        if let Some(cid_used) = self.freelist.pop() {
            cid = cid_used;
            let c = &mut self[cid];
            c.flags = Flag::empty();
            std::mem::swap(&mut c.lits, vec);
            c.search_from = 2;
        } else {
            cid = ClauseId::from(self.clause.len());
            let mut c = Clause {
                flags: Flag::empty(),
                ..Clause::default()
            };
            std::mem::swap(&mut c.lits, vec);
            self.clause.push(c);
        };

        let ClauseDB {
            #[cfg(feature = "bi_clause_completion")]
            ref mut bi_clause_completion_queue,
            ref mut clause,
            ref mut lbd_temp,
            ref mut bi_clause,
            ref ordinal,
            ref mut watch_cache,
            ..
        } = self;
        let c = &mut clause[cid.ordinal as usize];
        c.timestamp = *ordinal;
        let len2 = c.lits.len() == 2;
        if len2 {
            c.rank = 1;

            #[cfg(feature = "bi_clause_completion")]
            {
                for lit in c.iter() {
                    if !bi_clause_completion_queue.iter().any(|l| *l == *lit) {
                        bi_clause_completion_queue.push(*lit);
                    }
                }
            }
        } else {
            c.update_lbd(asg, lbd_temp);
        }
        if c.lits.len() <= 2 || (self.use_chan_seok && c.rank <= self.co_lbd_bound) {
            learnt = false;
        }
        if learnt {
            c.turn_on(Flag::LEARNT);
        }
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        if len2 {
            bi_clause[!l0].insert(l1, cid);
            bi_clause[!l1].insert(l0, cid);
        } else {
            watch_cache[!l0].insert_watch(cid, l1);
            watch_cache[!l1].insert_watch(cid, l0);
        }
        RefClause::Clause(cid)
    }
    /// remove a clause temporally
    fn detach_clause(&mut self, cid: ClauseId) -> (Lit, Lit) {
        let c = &self.clause[cid.ordinal as usize];
        assert!(1 < c.lits.len());
        let l0 = c.lit0();
        let l1 = c.lit1();
        if c.len() == 2 {
            self.bi_clause[!l0].remove(&l1);
            self.bi_clause[!l1].remove(&l0);
        } else {
            self.watch_cache[!l0].remove_watch(&cid);
            self.watch_cache[!l1].remove_watch(&cid);
        }
        (l0, l1)
    }
    /// push back a clause
    fn reattach_clause(&mut self, cid: ClauseId, (l0, l1): (Lit, Lit)) {
        let c = &self.clause[cid.ordinal as usize];
        if c.len() == 2 {
            self.bi_clause[!l0].insert(l1, cid);
            self.bi_clause[!l1].insert(l0, cid);
        } else {
            self.watch_cache[!l0].insert_watch(cid, l1);
            self.watch_cache[!l1].insert_watch(cid, l0);
        }
    }
    /// ## Warning
    /// this function is the only function that makes dead clauses
    fn remove_clause(&mut self, cid: ClauseId) {
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
        // if !self.clause[cid.ordinal as usize].is_dead() {
        // }
        let c = &mut self.clause[cid.ordinal as usize];
        debug_assert!(!c.is_dead());
        debug_assert!(1 < c.lits.len());
        remove_clause_fn(
            &mut self.certification_store,
            &mut self.bi_clause,
            &mut self.watch_cache,
            &mut self.num_bi_clause,
            &mut self.num_clause,
            &mut self.num_learnt,
            cid,
            c,
        );
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
    }
    fn remove_clause_sandbox(&mut self, cid: ClauseId) {
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
        let c = &mut self.clause[cid.ordinal as usize];
        debug_assert!(!c.is_dead());
        debug_assert!(1 < c.lits.len());
        let mut store = CertificationStore::default();
        let mut dummy1 = 1;
        let mut dummy2 = 1;
        let mut dummy3 = 1;
        remove_clause_fn(
            &mut store,
            &mut self.bi_clause,
            &mut self.watch_cache,
            &mut dummy1,
            &mut dummy2,
            &mut dummy3,
            cid,
            c,
        );
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is_dead()).count(), self.num_clause);
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
        debug_assert!(!self[cid].is_dead());
        assert!(1 < self[cid].len());
        let ClauseDB {
            ref mut clause,
            ref mut bi_clause,
            ref mut watch_cache,
            ref mut certification_store,
            ref mut num_bi_clause,
            ..
        } = self;
        let c = &mut clause[cid.ordinal as usize];
        // debug_assert!((*ch).lits.contains(&p));
        // debug_assert!(1 < (*ch).len());
        debug_assert!(1 < usize::from(!p));
        let lits = &mut c.lits;
        assert!(1 < lits.len());
        //
        //## Case:2-0
        //
        if lits.len() == 2 {
            if lits[0] == p {
                lits.swap(0, 1);
            }
            return RefClause::UnitClause(lits[0]);
        }

        (*c).search_from = 2;
        let mut new_lits: Vec<Lit> = lits
            .iter()
            .filter(|&l| *l != p)
            .copied()
            .collect::<Vec<Lit>>();
        if new_lits.len() == 2 {
            if let Some(reg) = bi_clause[!new_lits[0]].get(&new_lits[1]) {
                //
                //## Case:3-0
                //
                return RefClause::RegisteredClause(*reg);
            }
            //
            //## Case:3-2
            //
            let l0 = lits[0];
            let l1 = lits[1];
            std::mem::swap(lits, &mut new_lits);
            watch_cache[!l0].remove_watch(&cid);
            watch_cache[!l1].remove_watch(&cid);
            bi_clause[!lits[0]].insert(lits[1], cid);
            bi_clause[!lits[1]].insert(lits[0], cid);
            *num_bi_clause += 1;
            if certification_store.is_active() {
                certification_store.push_add(&c.lits);
                certification_store.push_delete(&new_lits);
            }
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
            if p == old_l0 || p == old_l1 {
                watch_cache[!p].remove_watch(&cid);
                watch_cache[!l1].insert_or_update_watch(cid, l0);
                // Here we assumed that there's no eliminated var in clause and *watch cache*.
                // Fortunately the current implementation purges all eliminated vars completely.
            } else {
                assert_eq!(old_l0, l0);
                assert_eq!(old_l1, l1);
            }
            if certification_store.is_active() {
                certification_store.push_add(&c.lits);
                certification_store.push_delete(&new_lits);
            }
            // self.watches(cid, "after strengthen_by_elimination case:3-3");
        }
        RefClause::Clause(cid)
    }
    fn transform_by_replacement(&mut self, cid: ClauseId, new_lits: &mut Vec<Lit>) -> RefClause {
        assert!(1 < new_lits.len());
        //
        //## Clause transform rules
        //
        // There are three cases:
        // 1. a normal clause is merged to a registered bi-clause. [Case:0]
        // 2. a normal clause becomes a new bi-clause.             [Case:2]
        // 3. a normal clause becomes a shorter normal clause.     [Case:3]
        //
        assert!(!self[cid].is_dead());
        let ClauseDB {
            clause,
            bi_clause,
            watch_cache,
            certification_store,
            ..
        } = self;
        let c = &mut clause[cid.ordinal as usize];
        debug_assert!(new_lits.len() < c.len());
        if new_lits.len() == 2 {
            if let Some(bc) = bi_clause[!new_lits[0]].get(&new_lits[1]) {
                let did = *bc;
                //
                //## Case:0
                //
                if certification_store.is_active() {
                    certification_store.push_delete(&new_lits);
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
            bi_clause[!l0].insert(l1, cid);
            bi_clause[!l1].insert(l0, cid);

            if certification_store.is_active() {
                certification_store.push_add(&new_lits);
                certification_store.push_delete(&c.lits);
            }
            c.turn_off(Flag::LEARNT);
            self.num_bi_clause += 1;

            if certification_store.is_active() {
                certification_store.push_add(&c.lits);
                certification_store.push_delete(&new_lits);
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

            if l0 == old_l0 && l1 == old_l1 {
            } else if l0 == old_l0 {
                watch_cache[!old_l1].remove_watch(&cid);
                watch_cache[!l0].insert_or_update_watch(cid, l1);
                watch_cache[!l1].insert_or_update_watch(cid, l0);
            } else if l0 == old_l1 {
                watch_cache[!old_l0].remove_watch(&cid);
                watch_cache[!l0].insert_or_update_watch(cid, l1);
                watch_cache[!l1].insert_or_update_watch(cid, l0);
            } else {
                watch_cache[!old_l0].remove_watch(&cid);
                watch_cache[!old_l1].remove_watch(&cid);
                watch_cache[!l0].insert_or_update_watch(cid, l1);
                watch_cache[!l1].insert_or_update_watch(cid, l0);
            }

            if certification_store.is_active() {
                certification_store.push_add(&new_lits);
                certification_store.push_delete(&c.lits);
            }
        }
        RefClause::Clause(cid)
    }
    fn transform_by_simplification<A>(&mut self, asg: &mut A, cid: ClauseId) -> RefClause
    where
        A: AssignIF,
    {
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
        debug_assert!(!self[cid].is_dead());
        // firstly sweep without consuming extra memory
        let mut need_to_shrink = false;
        for l in self[cid].iter() {
            debug_assert!(!asg.var(l.vi()).is(Flag::ELIMINATED));
            match asg.assigned(*l) {
                Some(true) => {
                    self.remove_clause(cid);
                    return RefClause::Dead;
                }
                Some(false) => {
                    need_to_shrink = true;
                }
                None if asg.var(l.vi()).is(Flag::ELIMINATED) => {
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
        let ClauseDB {
            clause,
            bi_clause,
            watch_cache,
            certification_store,
            ..
        } = self;
        let c = &mut clause[cid.ordinal as usize];
        let mut new_lits = c
            .lits
            .iter()
            .filter(|l| asg.assigned(**l).is_none() && !asg.var(l.vi()).is(Flag::ELIMINATED))
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
                if let Some(r) = bi_clause[!l0].get(&l1) {
                    let bid = *r;
                    //
                    //## Case:3-0
                    //
                    self.remove_clause(cid);
                    return RefClause::RegisteredClause(bid);
                }
                //
                //## Case:3-2
                //
                watch_cache[!c.lits[0]].remove_watch(&cid);
                watch_cache[!c.lits[1]].remove_watch(&cid);
                bi_clause[!l0].insert(l1, cid);
                bi_clause[!l1].insert(l0, cid);
                std::mem::swap(&mut c.lits, &mut new_lits);
                self.num_bi_clause += 1;
                c.turn_off(Flag::LEARNT);

                if certification_store.is_active() {
                    certification_store.push_add(&c.lits);
                    certification_store.push_delete(&new_lits);
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
                } else if old_l0 == l0 {
                    watch_cache[!old_l1].remove_watch(&cid);
                    watch_cache[!l0].insert_or_update_watch(cid, l1);
                    watch_cache[!l1].insert_or_update_watch(cid, l0);
                } else if old_l0 == l1 {
                    watch_cache[!old_l0].remove_watch(&cid);
                    watch_cache[!l0].insert_or_update_watch(cid, l1);
                    watch_cache[!l1].insert_or_update_watch(cid, l0);
                } else {
                    watch_cache[!old_l0].remove_watch(&cid);
                    watch_cache[!old_l1].remove_watch(&cid);
                    watch_cache[!l0].insert_or_update_watch(cid, l1);
                    watch_cache[!l1].insert_or_update_watch(cid, l0);
                }

                if certification_store.is_active() {
                    certification_store.push_add(&c.lits);
                    certification_store.push_delete(&new_lits);
                }
                RefClause::Clause(cid)
            }
        }
    }
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

        debug_assert!(old < 2);
        debug_assert!(1 < new);
        let ClauseDB {
            ref mut clause,
            ref mut watch_cache,
            ..
        } = self;
        let c = &mut clause[cid.ordinal as usize];
        let other = (old == 0) as usize;
        if !removed {
            //## Step:1
            watch_cache[!c.lits[old]].remove_watch(&cid);
        } else {
            debug_assert!(watch_cache[!c.lits[old]].get_watch(&cid).is_none());
        }
        //## Step:2
        watch_cache[!c.lits[new]].insert_watch(cid, c.lits[other]);

        #[cfg(feature = "maintain_watch_cache")]
        {
            //## Step:3
            watcher[!c.lits[other]].insert_or_update_watch(cid, c.lits[new]);
        }

        c.lits.swap(old, new);
    }
    fn mark_clause_as_used<A>(&mut self, asg: &mut A, cid: ClauseId) -> bool
    where
        A: AssignIF,
    {
        let chan_seok_condition = if self.use_chan_seok {
            self.co_lbd_bound as usize
        } else {
            0
        };
        let ClauseDB {
            ref mut clause,
            ref mut lbd_temp,
            ..
        } = self;
        let c = &mut clause[cid.ordinal as usize];
        let old_rank = c.rank as usize;
        let nlevels = c.update_lbd(asg, lbd_temp);
        debug_assert!(
            !c.is_dead(),
            "cdb.make_clause_as_dead received a dead clause"
        );
        if nlevels < old_rank {
            match (c.is(Flag::VIVIFIED2), c.is(Flag::VIVIFIED)) {
                _ if nlevels == 1 || nlevels + 1 < old_rank => {
                    c.turn_on(Flag::VIVIFIED2);
                    c.turn_off(Flag::VIVIFIED);
                }
                (false, false) => (),
                (false, true) => {
                    c.turn_on(Flag::VIVIFIED2);
                    c.turn_off(Flag::VIVIFIED);
                }
                (true, false) => c.turn_on(Flag::VIVIFIED),
                (true, true) => (),
            }
            // chan_seok_condition is zero if !use_chan_seok
            if c.is(Flag::LEARNT) {
                if nlevels < chan_seok_condition {
                    c.turn_off(Flag::LEARNT);
                    self.num_learnt -= 1;
                    return true;
                } else {
                    #[cfg(feature = "just_used")]
                    c.turn_on(Flag::JUST_USED);
                }
            }
        }
        false
    }
    fn reduce<A>(&mut self, asg: &mut A, nc: usize) -> bool
    where
        A: AssignIF,
    {
        #[cfg(feature = "clause_reduction")]
        if 0 == self.num_learnt {
            false
        } else {
            let go = if self.use_chan_seok {
                self.first_reduction < self.num_learnt
            } else {
                self.reduction_coeff * self.next_reduction <= nc
            };
            if go {
                self.reduction_coeff = ((nc as f64) / (self.next_reduction as f64)) as usize + 1;
                let nc = self.num_clause;
                self.reduce_db(asg, nc);
                return self.num_clause < nc;
            }
            false
        }
        #[cfg(not(feature = "clause_reduction"))]
        false
    }
    fn reset(&mut self) {
        debug_assert!(1 < self.clause.len());
        for (i, c) in &mut self.clause.iter_mut().enumerate().skip(1) {
            if c.is(Flag::LEARNT) && !c.is_dead() && (self.co_lbd_bound as usize) < c.lits.len() {
                remove_clause_fn(
                    &mut self.certification_store,
                    &mut self.bi_clause,
                    &mut self.watch_cache,
                    &mut self.num_bi_clause,
                    &mut self.num_clause,
                    &mut self.num_learnt,
                    ClauseId::from(i),
                    c,
                );
            }
        }
    }
    fn certificate_add_assertion(&mut self, lit: Lit) {
        self.certification_store.push_add(&[lit]);
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
        for (i, c) in self.clause.iter().enumerate().skip(1) {
            if c.is_dead() || (strict && c.is(Flag::LEARNT)) {
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
    fn minimize_with_bi_clauses<A>(&mut self, asg: &A, vec: &mut Vec<Lit>)
    where
        A: AssignIF,
    {
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
        for (_, &cid) in self.bi_clause[!l0].iter() {
            let c = &self.clause[cid.ordinal as usize];
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
    #[cfg(feature = "incremental_solver")]
    fn make_permanent_immortal(&mut self, cid: ClauseId) {
        self.eliminated_permanent
            .push(self.clause[cid.ordinal as usize].lits.clone());
    }
    fn watch_caches(&self, cid: ClauseId, mes: &str) -> (Lit, Lit) {
        // let mut _found = None;
        assert!(!cid.is_lifted_lit());
        let c = &self[cid];
        assert!(1 < c.len());
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        let l0_blocker: Option<Lit>;
        let l1_blocker: Option<Lit>;
        if 2 == c.lits.len() {
            assert!(
                self.bi_clause[!l0].contains_key(&l1),
                "(watch_cache health check: binary clause l0 not found){}, cid{}{:?}",
                mes,
                cid,
                c
            );
            assert!(
                self.bi_clause[!l1].contains_key(&l0),
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
            l0_blocker = Some(l1);
            l1_blocker = Some(l0);
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
            assert!(
                self.bi_clause[!l0].iter().all(|(_, c)| *c != cid),
                "(watch_cache health check: clause l0 found in binary_map){}, cid{}{:?}",
                mes,
                cid,
                c
            );
            assert!(
                self.bi_clause[!l1].iter().all(|(_, c)| *c != cid),
                "(watch_cache health check: clause l1 found in binary_map){}, cid{}{:?}",
                mes,
                cid,
                c
            );
            l0_blocker = self.watch_cache[!l0].get_watch(&cid).copied();
            l1_blocker = self.watch_cache[!l1].get_watch(&cid).copied();
        }
        (
            l0_blocker.map_or(Lit::default(), |b| b),
            l1_blocker.map_or(Lit::default(), |b| b),
        )
    }
    fn complete_bi_clauses<A>(&mut self, asg: &mut A)
    where
        A: AssignIF,
    {
        while let Some(lit) = self.bi_clause_completion_queue.pop() {
            self.complete_bi_clauses_with(asg, lit);
        }
    }
}

impl ClauseDB {
    /// formula: -a => b and b => c implies -a => c
    /// clause: [a, b] and [-b, c] deduces [a, c]
    /// map: [!a].get(b), [b].get(c), [!a].get(c)
    /// rename: [!lit].get(other), [other].get(third), [!a].get(third)
    fn complete_bi_clauses_with<A>(&mut self, asg: &mut A, lit: Lit)
    where
        A: AssignIF,
    {
        let mut vec: Vec<Vec<Lit>> = Vec::new();
        // [lit, other]
        for other in self.bi_clause[!lit].keys() {
            // [!other, third]
            for third in self.bi_clause[*other].keys() {
                if lit.vi() != third.vi() && !self.bi_clause[!lit].contains_key(&third) {
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
    /// assert!(cdb.has_bi_clause(l1, l2).is_some());
    /// assert!(cdb.has_bi_clause(!l1, l2).is_none());
    /// assert!(cdb.has_bi_clause(l1, !l2).is_none());
    /// assert!(cdb.has_bi_clause(!l1, !l2).is_none());
    ///```
    ///
    /// this is equivalent to the following:
    ///```ignore
    /// bi_clause[!l0].get(&l1).is_some()
    ///```
    fn has_bi_clause(&self, l0: Lit, l1: Lit) -> Option<ClauseId> {
        self.bi_clause[!l0].get(&l1).copied()
    }
    /// halve the number of 'learnt' or *removable* clauses.
    fn reduce_db<A>(&mut self, asg: &mut A, nc: usize)
    where
        A: AssignIF,
    {
        let ClauseDB {
            ref mut clause,
            ref co_lbd_bound,
            ref mut lbd_temp,
            ref ordinal,
            ref activity_decay,
            ref activity_anti_decay,
            ..
        } = self;
        self.num_reduction += 1;
        self.next_reduction += self.inc_step;
        let mut perm: Vec<OrderedProxy<usize>> = Vec::with_capacity(clause.len());
        for (i, c) in clause.iter_mut().enumerate().skip(1) {
            if !c.is(Flag::LEARNT) || c.is_dead() || asg.locked(c, ClauseId::from(i)) {
                continue;
            }

            #[cfg(feature = "just_used")]
            {
                let used = c.is(Flag::JUST_USED);
                if used {
                    c.turn_off(Flag::JUST_USED);
                    continue;
                }
            }

            // This is the best at least for 3SAT360.
            let rank = c.update_lbd(asg, lbd_temp) as f64;
            let act_v: f64 = c
                .lits
                .iter()
                .fold(0.0, |acc, l| acc.max(asg.activity(l.vi())));
            let act_c = c.update_activity(*ordinal, *activity_decay, *activity_anti_decay);
            let weight = rank / (act_v + act_c);
            perm.push(OrderedProxy::new(i, weight));
        }
        let keep = perm.len().min(nc) / 2;
        if !self.use_chan_seok {
            if clause[perm[keep].to()].rank <= 3 {
                self.next_reduction += 2 * self.extra_inc;
            }
            if clause[perm[0].to()].rank <= *co_lbd_bound {
                self.next_reduction += self.extra_inc;
            };
        }
        perm.sort();
        let thr = self.lbd_of_dp_ema.get() as u16;
        for i in &perm[keep..] {
            if thr <= self.clause[i.to()].rank {
                self.remove_clause(ClauseId::from(i.to()));
            }
        }
        debug_assert!(perm[0..keep].iter().all(|c| !self.clause[c.to()].is_dead()));
    }

    #[cfg(feature = "strategy_adaptation")]
    /// change good learnt clauses to permanent one.
    fn make_permanent(&mut self, reinit: bool) {
        // Adjusting for low decision levels.
        // move some clauses with good LBDs (col_lbd_bound) to Permanent
        let ClauseDB {
            ref mut clause,
            ref mut certificate_store,
            ..
        } = self;
        for c in &mut clause[1..] {
            if c.is_dead() || !c.is(Flag::LEARNT) {
                continue;
            }
            if c.rank < self.co_lbd_bound {
                c.turn_off(Flag::LEARNT);
                self.num_learnt -= 1;
            } else if reinit {
                if !c.is_dead() {
                    certificate_store.push_delete(&c.lits);
                    let l0 = c.lits[0];
                    let l1 = c.lits[1];
                    if c.len() == 2 {
                        self.bi_clause[!l0].remove(&l1);
                        self.bi_clause[!l1].remove(&l0);
                        self.num_bi_clause -= 1;
                    } else {
                        self.watcher[!l0].remove(&cid);
                        self.watcher[!l1].remove(&cid);
                    }
                    self.num_clause -= 1;
                    self.certification_store.push_delete(&c.lits);
                    c.lits.clear();
                }
            }
        }
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
fn remove_clause_fn(
    certificate_store: &mut CertificationStore,
    bi_clause: &mut [BiClause],
    watcher: &mut [WatchCache],
    num_bi_clause: &mut usize,
    num_clause: &mut usize,
    num_learnt: &mut usize,
    cid: ClauseId,
    c: &mut Clause,
) {
    debug_assert!(!c.is_dead());
    let l0 = c.lits[0];
    let l1 = c.lits[1];
    if c.len() == 2 {
        bi_clause[usize::from(!l0)].remove(&l1); // .expect("db1072");
        bi_clause[usize::from(!l1)].remove(&l0); // .expect("db1073");
        *num_bi_clause -= 1;
    } else {
        watcher[usize::from(!l0)].remove_watch(&cid); // .expect("db1076");
        watcher[usize::from(!l1)].remove_watch(&cid); // .expect("db1077");
    }
    if c.is(Flag::LEARNT) {
        *num_learnt -= 1;
    }
    *num_clause -= 1;
    certificate_store.push_delete(&c.lits);
    c.lits.clear();
}

impl Clause {
    fn update_activity(&mut self, t: usize, decay: f64, anti_decay: f64) -> f64 {
        if self.timestamp < t {
            let duration = (t - self.timestamp) as f64;
            self.reward *= decay.powf(duration);
            self.reward += anti_decay;
            self.timestamp = t;
        }
        self.reward
    }
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

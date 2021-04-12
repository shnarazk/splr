use {
    super::{property, CertificationStore, Clause, ClauseDB, ClauseDBIF, ClauseId, WatchDBIF},
    crate::{assign::AssignIF, solver::SolverEvent, types::*},
    std::{
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::{Iter, IterMut},
    },
};

impl Default for ClauseDB {
    fn default() -> ClauseDB {
        ClauseDB {
            clause: Vec::new(),
            bin_watcher: Vec::new(),
            watcher: Vec::new(),
            certification_store: CertificationStore::default(),
            soft_limit: 0, // 248_000_000
            use_chan_seok: false,
            co_lbd_bound: 4,
            // lbd_frozen_clause: 30,
            ordinal: 0,
            activity_decay: 0.99,
            activity_anti_decay: 0.01,
            activity_ema: Ema::new(1000),
            touched: Vec::new(),
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
            lbd_of_dp_ema: Ema::new(100_000),
            eliminated_permanent: Vec::new(),
        }
    }
}

impl Index<ClauseId> for ClauseDB {
    type Output = Clause;
    #[inline]
    fn index(&self, cid: ClauseId) -> &Clause {
        unsafe { self.clause.get_unchecked(cid.ordinal as usize) }
    }
}

impl IndexMut<ClauseId> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, cid: ClauseId) -> &mut Clause {
        unsafe { self.clause.get_unchecked_mut(cid.ordinal as usize) }
    }
}

impl Index<&ClauseId> for ClauseDB {
    type Output = Clause;
    #[inline]
    fn index(&self, cid: &ClauseId) -> &Clause {
        unsafe { self.clause.get_unchecked(cid.ordinal as usize) }
    }
}

impl IndexMut<&ClauseId> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, cid: &ClauseId) -> &mut Clause {
        unsafe { self.clause.get_unchecked_mut(cid.ordinal as usize) }
    }
}

impl Index<Range<usize>> for ClauseDB {
    type Output = [Clause];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Clause] {
        &self.clause[r]
    }
}

impl Index<RangeFrom<usize>> for ClauseDB {
    type Output = [Clause];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Clause] {
        &self.clause[r]
    }
}

impl IndexMut<Range<usize>> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Clause] {
        &mut self.clause[r]
    }
}

impl IndexMut<RangeFrom<usize>> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Clause] {
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
        let mut bin_watcher = Vec::with_capacity(2 * (nv + 1));
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        let mut touched = Vec::with_capacity(2 * (nv + 1));
        for _ in 0..2 * (nv + 1) {
            bin_watcher.push(Vec::new());
            watcher.push(Vec::new());
            touched.push(false);
        }
        ClauseDB {
            clause,
            bin_watcher,
            watcher,
            certification_store: CertificationStore::instantiate(config, cnf),
            soft_limit: config.c_cls_lim,
            activity_decay: config.crw_dcy_rat,
            activity_anti_decay: 1.0 - config.crw_dcy_rat,
            touched,
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
                self.bin_watcher.push(Vec::new());
                self.watcher.push(Vec::new());
                // for positive literal
                self.bin_watcher.push(Vec::new());
                self.watcher.push(Vec::new());
                // for negated literal
                self.touched.push(false);
                // for positive literal
                self.touched.push(false);
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
    fn bin_watcher_list(&self, l: Lit) -> &Vec<Watch> {
        &self.bin_watcher[l]
    }
    #[inline]
    fn bin_watcher_lists(&self) -> &[Vec<Watch>] {
        &self.bin_watcher
    }
    #[inline]
    fn watcher_list_mut(&mut self, l: Lit) -> &mut Vec<Watch> {
        &mut self.watcher[l]
    }
    #[inline]
    fn watcher_lists_mut(&mut self) -> &mut [Vec<Watch>] {
        &mut self.watcher
    }
    fn detach_watches(&mut self, cid: ClauseId) -> (Watch, Watch) {
        let ClauseDB {
            ref clause,
            ref mut watcher,
            ..
        } = self;
        let mut w1: Option<Watch> = None;
        let mut w2: Option<Watch> = None;
        let mut found = false;
        let lits = &clause[cid.ordinal as usize].lits;
        assert!(2 < lits.len());
        for l in lits.iter() {
            let w = watcher[!*l].detach_with(cid);
            if w.is_some() {
                if found {
                    w2 = w;
                    break;
                } else {
                    found = true;
                    w1 = w;
                }
            }
        }
        (w1.unwrap(), w2.unwrap())
    }
    fn update_watch(&mut self, cid: ClauseId, old: usize, new: usize, watch: Option<Watch>) {
        if old < 2 && new < 2 {
            self[cid].lits.swap(old, new);
            return;
        }
        assert!(old < 2);
        assert!(1 < new);
        let ClauseDB {
            ref mut clause,
            ref mut watcher,
            ..
        } = self;
        let c = &mut clause[cid.ordinal as usize];
        let other = (old == 0) as usize;
        let w1 = if let Some(w) = watch {
            // w.blocker = c.lits[other];
            w
        } else {
            watcher[!c.lits[old]].detach_with(cid).unwrap()
        };
        watcher[!c.lits[new]].register(w1);
        watcher[!c.lits[other]]
            .update_blocker(cid, c.lits[new])
            .unwrap();
        c.lits.swap(old, new);
        self.watches(cid, "eae");
    }
    fn garbage_collect(&mut self) {
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is(Flag::DEAD)).count(), self.num_clause);
        // debug_assert!(self.check_liveness1());
        let ClauseDB {
            ref mut bin_watcher,
            ref mut watcher,
            ref mut clause,
            ref mut touched,
            ..
        } = self;
        debug_assert_eq!(usize::from(!NULL_LIT), 1);
        //
        //## binary clauses
        //
        let (recycles, wss) = bin_watcher.split_at_mut(2);
        let recycled = &mut recycles[1];
        for (i, ws) in &mut wss.iter_mut().enumerate() {
            #[cfg(not(feature = "boundary_check"))]
            if !touched[i + 2] {
                continue;
            }
            let mut n = 0;
            while n < ws.len() {
                let cid = ws[n].c;
                let c = &mut clause[cid.ordinal as usize];
                if !c.is(Flag::DEAD) {
                    n += 1;
                    continue;
                }

                #[cfg(feature = "boundary_check")]
                assert!(touched[i + 2]);

                if !c.lits.is_empty() {
                    debug_assert!(c.is(Flag::DEAD));
                    recycled.push(Watch {
                        blocker: NULL_LIT,
                        c: cid,
                    });
                    assert!(0 < self.num_bi_clause);
                    self.num_bi_clause -= 1;
                    self.num_clause -= 1;
                    c.lits.clear();
                }
                ws.detach(n);
            }
        }

        //
        //## normal clauses
        //
        let (recycles, wss) = watcher.split_at_mut(2);
        let recycled = &mut recycles[1];
        for (i, ws) in &mut wss.iter_mut().enumerate() {
            #[cfg(not(feature = "boundary_check"))]
            if !touched[i + 2] {
                continue;
            }
            let mut n = 0;
            while n < ws.len() {
                let cid = ws[n].c;
                let c = &mut clause[cid.ordinal as usize];
                if !c.is(Flag::DEAD) {
                    n += 1;
                    continue;
                }

                #[cfg(feature = "boundary_check")]
                assert!(touched[i + 2]);

                if !c.lits.is_empty() {
                    debug_assert!(c.is(Flag::DEAD));
                    recycled.push(Watch {
                        blocker: NULL_LIT,
                        c: cid,
                    });
                    self.num_clause -= 1;
                    if c.is(Flag::LEARNT) {
                        self.num_learnt -= 1;
                    }
                    c.lits.clear();
                }
                ws.detach(n);
            }
            touched[i + 2] = false;
        }
    }
    /// return `true` if a binary clause [l0, l1] has been registered.
    ///```
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
    /// cdb.new_clause(&mut asg, &mut vec![l1, l2], false, false);
    /// cdb.new_clause(&mut asg, &mut vec![!l1, !l2, !l3], false, false);
    /// assert!(cdb.registered_bin_clause(l1, l2));
    /// assert!(!cdb.registered_bin_clause(!l1, l2));
    /// assert!(!cdb.registered_bin_clause(l1, !l2));
    /// assert!(!cdb.registered_bin_clause(!l1, !l2));
    ///```
    fn registered_bin_clause(&self, l0: Lit, l1: Lit) -> bool {
        for w in self.bin_watcher_list(!l0) {
            if w.blocker == l1 {
                return true;
            }
        }
        false
    }
    fn new_clause<A>(
        &mut self,
        asg: &mut A,
        vec: &mut Vec<Lit>,
        mut learnt: bool,
        level_sort: bool,
    ) -> ClauseId
    where
        A: AssignIF,
    {
        if level_sort {
            #[cfg(feature = "boundary_check")]
            debug_assert!(1 < vec.len());
            // // sort literals
            // let mut i_max = 1;
            // let mut lv_max = 0;
            // // seek a literal with max level
            // let level = asg.level_ref();
            // for (i, l) in vec.iter().enumerate() {
            //     let vi = l.vi();
            //     let lv = level[vi];
            //     if asg.assign(vi).is_some() && lv_max < lv {
            //         i_max = i;
            //         lv_max = lv;
            //     }
            // }
            // vec.swap(1, i_max);
        }
        self.certification_store.push_add(vec);
        let cid;
        if let Some(w) = self.watcher[!NULL_LIT].pop() {
            cid = w.c;
            let c = &mut self[cid];
            // if !c.is(Flag::DEAD) {
            //     println!("{} {:?}", cid.format(), vec2int(&c.lits));
            //     println!("len {}", self.watcher[NULL_LIT.negate() as usize].len());
            //     for w in &self.watcher[NULL_LIT.negate() as usize][..10] {
            //         if !self.clause[w.c].is(Flag::DEAD) {
            //             println!("{}", w.c.format());
            //         }
            //     }
            //     panic!("done");
            // }
            debug_assert!(c.is(Flag::DEAD));
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
        {
            let ClauseDB {
                ref mut clause,
                ref mut lbd_temp,
                ref mut num_clause,
                ref mut num_bi_clause,
                ref mut num_bi_learnt,
                ref mut num_lbd2,
                ref mut num_learnt,
                ref mut bin_watcher,
                ref ordinal,
                ref mut watcher,
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
            let l0 = c.lits[0];
            let l1 = c.lits[1];
            if len2 {
                assert_eq!(c.lits.len(), 2);
                *num_bi_clause += 1;
                bin_watcher[!l0].register(Watch {
                    blocker: l1,
                    c: cid,
                });
                bin_watcher[!l1].register(Watch {
                    blocker: l0,
                    c: cid,
                });
            } else {
                assert!(2 < c.lits.len());
                watcher[!l0].register(Watch {
                    blocker: l1,
                    c: cid,
                });
                watcher[!l1].register(Watch {
                    blocker: l0,
                    c: cid,
                });
            }
            *num_clause += 1;
        }
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is(Flag::DEAD)).count(), self.num_clause);
        self.watches(cid, "new_clause");
        cid
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
            !c.is(Flag::DEAD),
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
    /// ## Warning
    /// this function is the only function that turns `Flag::DEAD` on without calling
    /// `garbage_collect` which erases all the `DEAD` flags. So you must care about how and when
    /// `garbage_collect` is called.
    fn kill_clause(&mut self, cid: ClauseId) {
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is(Flag::DEAD)).count(), self.num_clause);
        let c = &mut self.clause[cid.ordinal as usize];
        debug_assert!(!c.is(Flag::DEAD));
        debug_assert!(1 < c.lits.len());
        if !c.is(Flag::DEAD) {
            c.kill(&mut self.touched);
        }
        self.certification_store.push_delete(&c.lits);
        // assert_eq!(self.clause.iter().skip(1).filter(|c| !c.is(Flag::DEAD)).count(), self.num_clause);
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
        for c in &mut self.clause[1..] {
            if c.is(Flag::LEARNT)
                && !c.is(Flag::DEAD)
                && (self.co_lbd_bound as usize) < c.lits.len()
            {
                c.kill(&mut self.touched);
            }
        }
        self.garbage_collect();
    }
    fn certificate_add_assertion(&mut self, lit: Lit) {
        self.certification_store.push_add(&[lit]);
    }
    fn certificate_save(&mut self) {
        self.certification_store.close();
    }
    fn touch_var(&mut self, vi: VarId) {
        self.touched[Lit::from_assign(vi, true)] = true;
        self.touched[Lit::from_assign(vi, false)] = true;
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
            if c.is(Flag::DEAD) || (strict && c.is(Flag::LEARNT)) {
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
    fn strengthen_by_elimination(&mut self, cid: ClauseId, p: Lit) -> bool {
        debug_assert!(!self[cid].is(Flag::DEAD));
        debug_assert!(1 < self[cid].len());
        self.watches(
            cid,
            &format!("before strengthen_by_elimination {}:{:?}", cid, &self[cid]),
        );
        let ClauseDB {
            ref mut clause,
            // ref mut bin_watcher,
            // ref mut watcher,
            ref mut certification_store,
            ..
        } = self;
        let c = &mut clause[cid.ordinal as usize];
        // debug_assert!((*ch).lits.contains(&p));
        // debug_assert!(1 < (*ch).len());
        if (*c).is(Flag::DEAD) {
            return false;
        }
        debug_assert!(1 < usize::from(!p));
        (*c).search_from = 2;
        let lits = &mut (*c).lits;
        debug_assert!(1 < lits.len());
        if lits.len() == 2 {
            if lits[0] == p {
                lits.swap(0, 1);
            }
            debug_assert!(1 < usize::from(!lits[0]));
            return true;
        }

        certification_store.push_delete(lits);

        // FIX THE LONGSTANDING BUG.
        // It was occured by failing to retrieve two `Watch`es.
        //
        // Since we can't hold an eliminated var in Watch::blocker
        // by following 'WATCHING LITERAL LIST MANAGEMENT RULES',
        // we have to update BOTH watching literals even if this is an O(n) operation.
        let l0 = lits[0];
        let l1 = lits[1];
        lits.retain(|&l| l != p);
        let mut mes = "strengthen_by_elimination";
        {
            if lits.len() == 2 {
                if l0 == lits[0] {
                    if l1 == lits[1] {
                        // move from watcher for l0 to bin_watcher for l0
                        let w0 = self.watcher[!l0].detach_with(cid).unwrap();
                        self.bin_watcher[!lits[0]].register(w0);
                        // move from watcher for l1 to bin_watcher for l1
                        let w1 = self.watcher[!l1].detach_with(cid).unwrap();
                        self.bin_watcher[!lits[1]].register(w1);
                    } else {
                        // update and move watcher for l0 to bin_watcher from l0
                        let mut w0 = self.watcher[!l0].detach_with(cid).unwrap();
                        w0.blocker = lits[1];
                        self.bin_watcher[!lits[0]].register(w0);
                        // update and move watcher for l1 to bin_watcher for lits[1]
                        let w1 = self.watcher[!l1].detach_with(cid).unwrap();
                        self.bin_watcher[!lits[1]].register(w1);
                    }
                } else if l1 == lits[0] {
                    if l0 == lits[1] {
                        // move from watcher for l0 to bin_watcher for l0
                        let w0 = self.watcher[!l0].detach_with(cid).unwrap();
                        self.bin_watcher[!lits[1]].register(w0);
                        // move from watcher for l1 to bin_watcher for l1
                        let w1 = self.watcher[!l1].detach_with(cid).unwrap();
                        self.bin_watcher[!lits[0]].register(w1);
                    } else {
                        // update and move watcher for l0 to bin_watcher for lits[1]
                        let mut w0 = self.watcher[!l0].detach_with(cid).unwrap();
                        w0.blocker = lits[0];
                        self.bin_watcher[!lits[1]].register(w0);
                        // update and move watcher for l1 to bin_watcher from l1
                        let mut w0 = self.watcher[!l1].detach_with(cid).unwrap();
                        w0.blocker = lits[1];
                        self.bin_watcher[!lits[0]].register(w0);
                    }
                } else {
                    dbg!(l0, l1, lits);
                    panic!("impossible");
                }
            } else if l0 == lits[0] {
                if l1 == lits[1] {
                    // nothing to do
                    mes = "db796";
                } else {
                    // update watch for l0
                    self.watcher[!lits[0]].update_blocker(cid, lits[1]).unwrap();
                    // update and move watch for l1 to wactch lits[1]
                    let mut w = self.watcher[!l1].detach_with(cid).unwrap();
                    w.blocker = lits[0];
                    self.watcher[!lits[1]].register(w);
                }
            } else if l1 == lits[0] {
                if l0 == lits[1] {
                    // nothing to do
                    mes = "db808";
                } else {
                    // update watch for l1
                    self.watcher[!lits[0]].update_blocker(cid, lits[1]).unwrap();
                    // update and move watch for l0 to watch for lits[1]
                    let mut w = self.watcher[!l0].detach_with(cid).unwrap();
                    w.blocker = lits[0];
                    self.watcher[!lits[1]].register(w);
                }
            } else {
                panic!("impossible");
            }
        }
        /* {
        let mut w1: Option<Watch> = None;
        let mut w2: Option<Watch> = None;
        let mut found = false;
        for l in lits.iter() {
            let w = watcher[!*l].detach_with(cid);
            if w.is_some() {
                if found {
                    w2 = w;
                    break;
                } else {
                    found = true;
                    w1 = w;
                }
            }
        }

        lits.delete_unstable(|&x| x == p);
        let q = lits[0];
        let r = lits[1];
        match (w1, w2) {
            (Some(mut w1), Some(mut w2)) => {
                w1.blocker = r;
                w2.blocker = q;
                if lits.len() == 2 {
                    bin_watcher[!q].register(w1);
                    bin_watcher[!r].register(w2);
                    self.num_bi_clause += 1;
                    if c.is(Flag::LEARNT) {
                        c.turn_off(Flag::LEARNT);
                        c.rank = 1;
                        self.num_learnt -= 1;
                        self.num_bi_learnt += 1;
                    }
                } else {
                    watcher[!q].register(w1);
                    watcher[!r].register(w2);
                }
            }
            _ => panic!("fix me"),
        }
        } */
        certification_store.push_add(&c.lits);
        self.watches(cid, mes);
        false
    }
    fn minimize_with_biclauses<A>(&mut self, asg: &A, vec: &mut Vec<Lit>)
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
        let mut nsat = 0;
        for w in &self.bin_watcher[!l0] {
            let c = &self.clause[w.c.ordinal as usize];
            debug_assert!(c[0] == l0 || c[1] == l0);
            let other = c[(c[0] == l0) as usize];
            let vi = other.vi();
            if self.lbd_temp[vi] == key && asg.assigned(other) == Some(true) {
                nsat += 1;
                self.lbd_temp[vi] = key - 1;
            }
        }
        if 0 < nsat {
            self.lbd_temp[l0.vi()] = key;
            vec.retain(|l| self.lbd_temp[l.vi()] == key);
        }
    }
    #[cfg(feature = "incremental_solver")]
    fn make_permanent_immortal(&mut self, cid: ClauseId) {
        self.eliminated_permanent
            .push(self.clause[cid.ordinal as usize].lits.clone());
    }
    fn watches(&self, cid: ClauseId, mes: &str) -> (Lit, Lit) {
        // let mut _found = None;
        let c = &self[cid];
        let l0 = c.lits[0];
        let l1 = c.lits[1];
        if 2 == c.lits.len() {
            assert!(
                self.bin_watcher[!l0].iter().any(|w| w.c == cid),
                "(a){}",
                mes
            );
            assert!(
                self.bin_watcher[!l1].iter().any(|w| w.c == cid),
                "(b){}",
                mes
            );
            // for (i, wl) in self.bin_watcher.iter().enumerate() {
            //     if wl.iter().any(|w| w.c == cid) {
            //         if let Some(f) = found {
            //             return (f, Lit::from(i));
            //         }
            //         found = Some(Lit::from(i));
            //     }
            // }
        } else {
            assert!(self.watcher[!l0].iter().any(|w| w.c == cid), "(c){}", mes);
            assert!(self.watcher[!l1].iter().any(|w| w.c == cid), "(d){}", mes);
            // for (i, wl) in self.watcher.iter().enumerate() {
            //     if let Some(w) = wl.iter().find(|w| w.c == cid) {
            //         let watch = Lit::from(i);
            //         assert_ne!(watch, Lit::default());
            //         assert_ne!(watch, Lit::default());
            //         if !(!watch == l0 || !watch == l1) {
            //             dbg!((cid, l0, l1, w));
            //             panic!("done");
            //         }
            //         assert!(!watch == l0 || !watch == l1);
            //         if let Some(f) = found {
            //             let w0 = f;
            //             let w1 = Lit::from(i);
            //             assert_ne!(w0, w1);
            //             return (w0, w1);
            //         }
            //         // assert!(w.blocker == l0 || w.blocker == l1);
            //         found = Some(Lit::from(i));
            //     }
            // }
        }
        (Lit::default(), Lit::default())
    }
}

impl ClauseDB {
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
            if !c.is(Flag::LEARNT) || c.is(Flag::DEAD) || asg.locked(c, ClauseId::from(i)) {
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
                self.kill_clause(ClauseId::from(i.to()));
            }
        }
        debug_assert!(perm[0..keep]
            .iter()
            .all(|c| !self.clause[c.to()].is(Flag::DEAD)));
        self.garbage_collect();
    }

    #[cfg(feature = "strategy_adaptation")]
    /// change good learnt clauses to permanent one.
    fn make_permanent(&mut self, reinit: bool) {
        // Adjusting for low decision levels.
        // move some clauses with good LBDs (col_lbd_bound) to Permanent
        let ClauseDB {
            ref mut clause,
            ref mut certicate_store,
            ..
        } = self;
        for c in &mut clause[1..] {
            if c.is(Flag::DEAD) || !c.is(Flag::LEARNT) {
                continue;
            }
            if c.rank < self.co_lbd_bound {
                c.turn_off(Flag::LEARNT);
                self.num_learnt -= 1;
            } else if reinit {
                certicate_store.push_delete(&c.lits);
                c.kill(&mut self.touched);
            }
        }
        self.garbage_collect();
    }
    pub fn has_consistent_watcher<A>(&self, asg: &A, cid: ClauseId) -> bool
    where
        A: AssignIF,
    {
        let mut found = 0;
        let lits = &self.clause[cid.ordinal as usize].lits;
        let is_2 = lits.len() == 2;
        for (l, wl) in self.bin_watcher.iter().enumerate().skip(2) {
            for w in wl.iter() {
                if w.c == cid {
                    if !is_2 {
                        return false;
                    }
                    if asg.var(w.blocker.vi()).is(Flag::ELIMINATED) {
                        return false;
                    }
                    if !lits.contains(&w.blocker) || !lits.contains(&!Lit::from(l)) {
                        return false;
                    }
                    found += 1;
                }
            }
        }
        for (l, wl) in self.watcher.iter().enumerate().skip(2) {
            for w in wl.iter() {
                if w.c == cid {
                    if is_2 {
                        return false;
                    }
                    if asg.var(w.blocker.vi()).is(Flag::ELIMINATED) {
                        return false;
                    }
                    if !lits.contains(&w.blocker) || !lits.contains(&!Lit::from(l)) {
                        return false;
                    }
                    found += 1;
                }
            }
        }
        found == 2
    }
    pub fn check_consistency<A>(&self, asg: &A, msg: &str)
    where
        A: AssignIF,
    {
        /* if let Some(cid) = self.validate(asg.assign_ref(), false) */
        {
            let mut hash: std::collections::HashMap<u32, usize> = std::collections::HashMap::new();
            /* for (l, wl) in self.bin_watcher.iter().enumerate().skip(2) {
                for w in wl.iter() {
                    let c = &self[w.c];
                    if c.lits.len() != 2 {
                        dbg!((l, w.blocker, w.c, &c.lits));
                        panic!("aoa")
                    }

                    if !c.lits.contains(&w.blocker) || !c.lits.contains(&!Lit::from(l)) {
                        dbg!((l, w.blocker, w.c, &c.lits));
                        panic!("found");
                    }
                    *hash.entry(w.c.ordinal).or_insert(0) += 1;
                }
            } */
            for (l, wl) in self.watcher.iter().enumerate().skip(2) {
                for w in wl.iter() {
                    let c = &self[w.c];
                    if c.lits.len() == 2 {
                        dbg!((l, w.blocker, w.c, &c.lits));
                        panic!("found");
                    }
                    if !c.lits.contains(&w.blocker) || !c.lits.contains(&!Lit::from(l)) {
                        dbg!((l, w.blocker, w.c, &c.lits));
                        panic!("found after {}", msg);
                    }
                    *hash.entry(w.c.ordinal).or_insert(0) += 1;
                }
            }
            for (cid, n) in hash.iter() {
                let c = &self.clause[*cid as usize];
                if c.is(Flag::DEAD) {
                    continue;
                }
                assert!(*n == 2 || *n == 0);
            }
            for (cid, c) in self.clause.iter().enumerate().skip(1) {
                if c.is(Flag::DEAD) {
                    continue;
                }
                if !self.has_consistent_watcher(
                    asg,
                    ClauseId {
                        ordinal: cid as u32,
                    },
                ) {
                    panic!("{}{:?} doesn't have a valid watches", cid, c);
                }
            }
        }
        if let Some(cid) = self.validate(asg.assign_ref(), false) {
            panic!(
                "{:?}{:?} is falsified {}!",
                cid,
                &self[cid],
                self.has_consistent_watcher(asg, cid),
            );
        }
    }
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
    /// make a clause *dead*; the clause still exists in clause database as a garbage.
    fn kill(&mut self, touched: &mut [bool]) {
        self.turn_on(Flag::DEAD);
        debug_assert!(1 < usize::from(self.lits[0]) && 1 < usize::from(self.lits[1]));
        touched[!self.lits[0]] = true;
        touched[!self.lits[1]] = true;
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

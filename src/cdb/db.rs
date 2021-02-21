#[cfg(feature = "strategy_adaptation")]
use crate::state::SearchStrategy;
use {
    super::{CertifiedRecord, Clause, ClauseDB, ClauseId, WatchDBIF},
    crate::{assign::AssignIF, solver::SolverEvent, types::*},
    std::{
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::{Iter, IterMut},
    },
};

/// API for clause management like [`reduce`](`crate::cdb::ClauseDBIF::reduce`), [`new_clause`](`crate::cdb::ClauseDBIF::new_clause`), [`watcher_list`](`crate::cdb::ClauseDBIF::watcher_list`), and so on.
pub trait ClauseDBIF: ActivityIF<ClauseId> + IndexMut<ClauseId, Output = Clause> {
    /// return the length of `clause`.
    fn len(&self) -> usize;
    /// return true if it's empty.
    fn is_empty(&self) -> bool;
    /// return an iterator.
    fn iter(&self) -> Iter<'_, Clause>;
    /// return a mutable iterator.
    fn iter_mut(&mut self) -> IterMut<'_, Clause>;
    /// return the list of bin_watch lists
    fn bin_watcher_lists(&self) -> &[Vec<Watch>];
    /// return a watcher list
    fn watcher_list(&self, l: Lit) -> &[Watch];
    /// return the list of watch lists
    fn watcher_lists_mut(&mut self) -> &mut [Vec<Watch>];
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn detach(&mut self, cid: ClauseId);
    /// check a condition to reduce.
    /// * return `true` if reduction is done.
    /// * Otherwise return `false`.
    ///
    /// # CAVEAT
    /// *precondition*: decision level == 0.
    fn reduce<A>(&mut self, asg: &mut A, nc: usize) -> bool
    where
        A: AssignIF;
    fn reset(&mut self);
    /// delete *dead* clauses from database, which are made by:
    /// * `reduce`
    /// * `simplify`
    /// * `kill`
    fn garbage_collect(&mut self);
    /// return `true` if a literal pair `(l0, l1)` is registered.
    fn registered_bin_clause(&self, l0: Lit, l1: Lit) -> bool;
    /// allocate a new clause and return its id.
    /// * If `level_sort` is on, register `v` as a learnt after sorting based on assign level.
    /// * Otherwise, register `v` as a permanent clause, which rank is zero.
    fn new_clause<A>(
        &mut self,
        asg: &mut A,
        v: &mut Vec<Lit>,
        learnt: bool,
        level_sort: bool,
    ) -> ClauseId
    where
        A: AssignIF;
    /// update LBD then convert a learnt clause to permanent if needed.
    fn mark_clause_as_used<A>(&mut self, asg: &mut A, cid: ClauseId) -> bool
    where
        A: AssignIF;
    /// return the number of alive clauses in the database.
    fn count(&self) -> usize;
    /// return the number of clauses which satisfy given flags and aren't DEAD.
    fn countf(&self, mask: Flag) -> usize;
    /// record a clause to unsat certification.
    fn certificate_add(&mut self, vec: &[Lit]);
    /// record a deleted clause to unsat certification.
    fn certificate_delete(&mut self, vec: &[Lit]);
    /// flag positive and negative literals of a var as dirty
    fn touch_var(&mut self, vi: VarId);
    /// check the number of clauses
    /// * `Err(SolverError::OutOfMemory)` -- the db size is over the limit.
    /// * `Ok(true)` -- enough small
    /// * `Ok(false)` -- close to the limit
    fn check_size(&self) -> Result<bool, SolverError>;
    /// returns None if the given assignment is a model of a problem.
    /// Otherwise returns a clause which is not satisfiable under a given assignment.
    /// Clauses with an unassigned literal are treated as falsified in `strict` mode.
    fn validate(&self, model: &[Option<bool>], strict: bool) -> Option<ClauseId>;
    /// removes Lit `p` from Clause *self*. This is an O(n) function!
    /// This returns `true` if the clause became a unit clause.
    /// And this is called only from `Eliminator::strengthen_clause`.
    fn strengthen(&mut self, cid: ClauseId, p: Lit) -> bool;
    /// minimize a clause.
    fn minimize_with_biclauses<A>(&mut self, asg: &A, vec: &mut Vec<Lit>)
    where
        A: AssignIF;

    #[cfg(feature = "incremental_solver")]
    /// save an eliminated permanent clause to an extra space for incremental solving.
    fn make_permanent_immortal(&mut self, cid: ClauseId);
}

impl Default for ClauseDB {
    fn default() -> ClauseDB {
        ClauseDB {
            clause: Vec::new(),
            bin_watcher: Vec::new(),
            watcher: Vec::new(),
            certified: Vec::new(),
            soft_limit: 0, // 248_000_000
            use_chan_seok: false,
            co_lbd_bound: 5,
            // lbd_frozen_clause: 30,
            ordinal: 0,
            activity_inc: 1.0,
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
            num_active: 0,
            num_bi_clause: 0,
            num_bi_learnt: 0,
            num_lbd2: 0,
            num_learnt: 0,
            num_reduction: 0,
            during_vivification: false,
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
        let mut certified = Vec::new();
        if config.use_certification {
            certified.push((CertifiedRecord::SENTINEL, Vec::new()));
        }
        ClauseDB {
            clause,
            bin_watcher,
            watcher,
            certified,
            soft_limit: config.c_cls_lim,
            activity_decay: config.crw_dcy_rat,
            activity_anti_decay: 1.0 - config.crw_dcy_rat,
            touched,
            lbd_temp: vec![0; nv + 1],
            reducible: config.use_reduce(),

            ..ClauseDB::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        match e {
            #[cfg(feature = "strategy_adaptation")]
            SolverEvent::Adapt(strategy, num_conflict) => {
                // # PRECONDITION
                // decision level must be 0 if `state.strategy.1` == `state[Stat::Conflict]`
                match strategy {
                    (_, n) if n != num_conflict => (),
                    (SearchStrategy::Initial, _) => (),
                    (SearchStrategy::Generic, _) => (),
                    (SearchStrategy::LowDecisions, _) => {
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
                    (SearchStrategy::HighSuccessive, _) => {
                        self.co_lbd_bound = 3;
                        self.first_reduction = 30000;
                        self.use_chan_seok = true;
                        // This call requires 'decision level == 0'.
                        self.make_permanent(false);
                    }
                    (SearchStrategy::LowSuccessive, _) => (),
                    (SearchStrategy::ManyGlues, _) => (),
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
            SolverEvent::Vivify(on) => {
                self.during_vivification = on;
            }
            _ => (),
        }
    }
}

impl Export<(usize, usize, usize, usize, usize, usize), bool> for ClauseDB {
    /// exports:
    ///  1. the number of active clauses
    ///  1. the number of binary clauses
    ///  1. the number of binary learnt clauses
    ///  1. the number of clauses which LBDs are 2
    ///  1. the number of learnt clauses
    ///  1. the number of clause reductions
    ///
    ///```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use crate::splr::cdb::ClauseDB;
    /// let cdb = ClauseDB::instantiate(&Config::default(), &CNFDescription::default());
    /// let (_active, _bi_clause, _bi_learnt, _lbd2, _learnt, _reduction) = cdb.exports();
    ///```
    #[inline]
    fn exports(&self) -> (usize, usize, usize, usize, usize, usize) {
        (
            self.num_active,
            self.num_bi_clause,
            self.num_bi_learnt,
            self.num_lbd2,
            self.num_learnt,
            self.num_reduction,
        )
    }
    /// return the value of `use_chan_seok`
    fn mode(&self) -> bool {
        self.use_chan_seok
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
    fn watcher_list(&self, l: Lit) -> &[Watch] {
        &self.watcher[l]
    }
    #[inline]
    fn bin_watcher_lists(&self) -> &[Vec<Watch>] {
        &self.bin_watcher
    }
    #[inline]
    fn watcher_lists_mut(&mut self) -> &mut [Vec<Watch>] {
        &mut self.watcher
    }
    fn garbage_collect(&mut self) {
        // debug_assert!(self.check_liveness1());
        let ClauseDB {
            ref mut bin_watcher,
            ref mut watcher,
            ref mut clause,
            ref mut touched,
            ref mut certified,
            ..
        } = self;
        debug_assert_eq!(usize::from(!NULL_LIT), 1);
        //
        //## binary clauses
        //
        let (recycles, wss) = bin_watcher.split_at_mut(2);
        let recycled = &mut recycles[1];
        for (i, ws) in &mut wss.iter_mut().enumerate() {
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
                if !c.lits.is_empty() {
                    debug_assert!(c.is(Flag::DEAD));
                    recycled.push(Watch {
                        blocker: NULL_LIT,
                        c: cid,
                    });
                    if c.is(Flag::LEARNT) {
                        self.num_learnt -= 1;
                    }
                    if !certified.is_empty() && !c.is(Flag::VIV_ASSUMED) {
                        let temp = c.lits.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
                        debug_assert!(!temp.is_empty());
                        certified.push((CertifiedRecord::DELETE, temp));
                    }
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
            if !touched[i + 2] {
                continue;
            }
            touched[i + 2] = false;
            let mut n = 0;
            while n < ws.len() {
                let cid = ws[n].c;
                let c = &mut clause[cid.ordinal as usize];
                if !c.is(Flag::DEAD) {
                    n += 1;
                    continue;
                }
                if !c.lits.is_empty() {
                    debug_assert!(c.is(Flag::DEAD));
                    recycled.push(Watch {
                        blocker: NULL_LIT,
                        c: cid,
                    });
                    if c.is(Flag::LEARNT) {
                        self.num_learnt -= 1;
                    }
                    if !certified.is_empty() && !c.is(Flag::VIV_ASSUMED) {
                        let temp = c.lits.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
                        debug_assert!(!temp.is_empty());
                        certified.push((CertifiedRecord::DELETE, temp));
                    }
                    c.lits.clear();
                }
                ws.detach(n);
            }
        }
        self.num_active = self.clause.len() - recycled.len();
        // debug_assert!(self.check_liveness2());
    }
    fn registered_bin_clause(&self, l0: Lit, l1: Lit) -> bool {
        for w in &self.bin_watcher_lists()[usize::from(!l0)] {
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
        if !self.certified.is_empty() && !self.during_vivification {
            let temp = vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
            debug_assert!(!temp.is_empty());
            self.certified.push((CertifiedRecord::ADD, temp));
        }
        let cid;
        let l0 = vec[0];
        let l1 = vec[1];
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
        if self.during_vivification {
            self[cid].turn_on(Flag::VIV_ASSUMED);
        }
        {
            let ClauseDB {
                ref mut clause,
                ref mut lbd_temp,
                ref mut num_active,
                ref mut num_bi_clause,
                ref mut num_bi_learnt,
                ref mut num_lbd2,
                ref mut num_learnt,
                ref mut bin_watcher,
                ref mut watcher,
                ..
            } = self;
            let c = &mut clause[cid.ordinal as usize];
            c.update_lbd(asg, lbd_temp);
            let len2 = c.lits.len() == 2;
            if c.lits.len() <= 2 || (self.use_chan_seok && c.rank as usize <= self.co_lbd_bound) {
                learnt = false;
            }
            if learnt {
                c.turn_on(Flag::LEARNT);

                if len2 {
                    *num_bi_learnt += 1;
                }
                if c.rank <= 2 {
                    *num_lbd2 += 1;
                }
                *num_learnt += 1;
            }
            if len2 {
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
                watcher[!l0].register(Watch {
                    blocker: l1,
                    c: cid,
                });
                watcher[!l1].register(Watch {
                    blocker: l0,
                    c: cid,
                });
            }
            *num_active += 1;
        }
        cid
    }
    fn mark_clause_as_used<A>(&mut self, asg: &mut A, cid: ClauseId) -> bool
    where
        A: AssignIF,
    {
        let chan_seok_condition = if self.use_chan_seok {
            self.co_lbd_bound
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
        debug_assert!(!c.is(Flag::DEAD), format!("found {} is dead: {}", cid, c));
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
    fn count(&self) -> usize {
        self.clause.len() - self.watcher[!NULL_LIT].len() - 1
    }
    fn countf(&self, mask: Flag) -> usize {
        self.clause
            .iter()
            .skip(1)
            .filter(|&c| c.flags.contains(mask) && !c.flags.contains(Flag::DEAD))
            .count()
    }
    /// ## Warning
    /// this function is the only function that turns `Flag::DEAD` on without calling
    /// `garbage_collect` which erases all the `DEAD` flags. So you must care about how and when
    /// `garbage_collect` is called.
    fn detach(&mut self, cid: ClauseId) {
        let c = &mut self.clause[cid.ordinal as usize];
        debug_assert!(!c.is(Flag::DEAD));
        debug_assert!(1 < c.lits.len());
        c.kill(&mut self.touched);
    }
    fn reduce<A>(&mut self, asg: &mut A, nc: usize) -> bool
    where
        A: AssignIF,
    {
        if !self.reducible || 0 == self.num_learnt {
            return false;
        }
        let go = if self.use_chan_seok {
            self.first_reduction < self.num_learnt
        } else {
            self.reduction_coeff * self.next_reduction <= nc
        };
        if go {
            self.reduction_coeff = ((nc as f64) / (self.next_reduction as f64)) as usize + 1;
            self.reduce_db(asg, nc);
        }
        go
    }
    fn reset(&mut self) {
        debug_assert!(1 < self.clause.len());
        for c in &mut self.clause[1..] {
            if c.is(Flag::LEARNT) && !c.is(Flag::DEAD) && self.co_lbd_bound < c.lits.len() {
                c.kill(&mut self.touched);
            }
        }
        self.garbage_collect();
    }
    fn certificate_add(&mut self, vec: &[Lit]) {
        if !self.certified.is_empty() && !self.during_vivification {
            let temp = vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
            debug_assert!(!temp.is_empty());
            self.certified.push((CertifiedRecord::ADD, temp));
        }
    }
    fn certificate_delete(&mut self, vec: &[Lit]) {
        if !self.certified.is_empty() && !self.during_vivification {
            let temp = vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
            self.certified.push((CertifiedRecord::DELETE, temp));
        }
    }
    fn touch_var(&mut self, vi: VarId) {
        self.touched[Lit::from_assign(vi, true)] = true;
        self.touched[Lit::from_assign(vi, false)] = true;
    }
    fn check_size(&self) -> Result<bool, SolverError> {
        if self.soft_limit == 0 || self.len() <= self.soft_limit {
            Ok(0 == self.soft_limit || 4 * self.count() < 3 * self.soft_limit)
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
    fn strengthen(&mut self, cid: ClauseId, p: Lit) -> bool {
        debug_assert!(!self[cid].is(Flag::DEAD));
        debug_assert!(1 < self[cid].len());
        let c = &mut self[cid];
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
        if lits[0] == p || lits[1] == p {
            let (q, r) = if lits[0] == p {
                lits.swap_remove(0);
                (lits[0], lits[1])
            } else {
                lits.swap_remove(1);
                (lits[1], lits[0])
            };
            debug_assert!(1 < usize::from(!p));
            if 2 == lits.len() {
                let mut w1 = self.watcher[!p].detach_with(cid);
                w1.blocker = r;
                let mut w2 = self.watcher[!r].detach_with(cid);
                w2.blocker = q;
                self.bin_watcher[!q].register(w1);
                self.bin_watcher[!r].register(w2);
            } else {
                let mut w0 = self.watcher[!p].detach_with(cid);
                w0.blocker = r;
                self.watcher[!q].register(w0);
                self.watcher[!r].update_blocker(cid, q);
            }
        } else {
            lits.delete_unstable(|&x| x == p);
            if 2 == lits.len() {
                let q = lits[0];
                let r = lits[1];
                let mut w1 = self.watcher[!q].detach_with(cid);
                w1.blocker = r;
                let mut w2 = self.watcher[!r].detach_with(cid);
                w2.blocker = q;
                self.bin_watcher[!q].register(w1);
                self.bin_watcher[!r].register(w2);
            }
        }
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
}

impl ClauseDB {
    /// halve the number of 'learnt' or *removable* clauses.
    fn reduce_db<A>(&mut self, asg: &mut A, nc: usize)
    where
        A: AssignIF,
    {
        let ClauseDB {
            ref mut clause,
            ref mut lbd_temp,
            ref mut touched,
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

            let mut act_v: f64 = 0.0;
            for l in c.lits.iter() {
                act_v = act_v.max(asg.activity(l.vi()));
            }
            let rank = c.update_lbd(asg, lbd_temp) as f64;
            let act_c = c.update_activity(*ordinal, *activity_decay, *activity_anti_decay);
            let weight = rank / (act_v + act_c);
            perm.push(OrderedProxy::new(i, weight));
        }
        let keep = (perm.len() / 2).min(nc / 2);
        if !self.use_chan_seok {
            if clause[perm[keep].to()].rank <= 3 {
                self.next_reduction += self.extra_inc;
            }
            if clause[perm[0].to()].rank <= 5 {
                self.next_reduction += self.extra_inc;
            };
        }
        perm.sort_unstable();
        for i in &perm[keep..] {
            let c = &mut clause[i.to()];
            if 2 < c.rank {
                c.kill(touched);
            }
        }
        debug_assert!(perm[0..keep].iter().all(|c| !clause[c.to()].is(Flag::DEAD)));
        self.garbage_collect();
    }

    #[cfg(feature = "strategy_adaptation")]
    /// change good learnt clauses to permanent one.
    fn make_permanent(&mut self, reinit: bool) {
        // Adjusting for low decision levels.
        // move some clauses with good LBDs (col_lbd_bound) to Permanent
        for c in &mut self.clause[1..] {
            if c.is(Flag::DEAD) || !c.is(Flag::LEARNT) {
                continue;
            }
            if c.rank <= self.co_lbd_bound as u16 {
                c.turn_off(Flag::LEARNT);
                self.num_learnt -= 1;
            } else if reinit {
                c.kill(&mut self.touched);
            }
        }
        self.garbage_collect();
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

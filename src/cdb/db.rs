use {
    super::{CertifiedRecord, Clause, ClauseDB, ClauseId, WatchDBIF, WatchList, LBDIF},
    crate::{assign::AssignIF, solver::SolverEvent, state::SearchStrategy, types::*},
    std::{
        collections::BinaryHeap,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::{Iter, IterMut},
    },
};

const ACTIVITY_SCALE: f64 = 10_000_000.0;

/// API for clause management like `reduce`, `simplify`, `new_clause`, and so on.
pub trait ClauseDBIF: IndexMut<ClauseId, Output = Clause> {
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
    fn watcher_list(&self, l: Lit) -> &WatchList;
    /// return the list of watch lists
    fn watcher_lists_mut(&mut self) -> &mut [WatchList];
    /// unregister a clause `cid` from clause database and make the clause dead.
    fn detach(&mut self, cid: ClauseId);
    /// check a condition to reduce.
    /// * return `true` if reduction is done.
    /// * Otherwise return `false`.
    ///
    /// # CAVEAT
    /// *precondition*: decision level == 0.
    fn check_and_reduce<A>(&mut self, asg: &mut A, nc: usize, average: f64) -> bool
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
    /// save an eliminated permanent clause to an extra space for incremental solving.
    #[cfg(feature = "incremental_solver")]
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
            touched: Vec::new(),
            lbd_temp: Vec::new(),
            num_lbd_update: 0,
            inc_step: 300,
            extra_inc: 1000,
            first_reduction: 1000,
            last_reduction: 0,
            next_reduction: 1000,
            reducable: true,
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

impl ActivityIF for ClauseDB {
    type Ix = ClauseId;
    type Inc = f64;
    fn activity(&mut self, cid: Self::Ix) -> f64 {
        (self.clause[cid.ordinal as usize].reward as f64) / ACTIVITY_SCALE
    }
    fn set_activity(&mut self, cid: Self::Ix, val: Self::Inc) {
        self.clause[cid.ordinal as usize].reward = (val * ACTIVITY_SCALE) as usize;
    }
    fn bump_activity(&mut self, _cid: Self::Ix, _: Self::Inc) {}
    fn scale_activity(&mut self) {}
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
            watcher.push(BinaryHeap::<Watch>::new());
            touched.push(false);
        }
        let mut certified = Vec::new();
        if config.use_certification {
            certified.push((CertifiedRecord::SENTINEL, Vec::new()));
        }
        ClauseDB {
            clause,
            touched,
            lbd_temp: vec![0; nv + 1],
            bin_watcher,
            watcher,
            certified,
            reducable: config.use_reduce(),
            soft_limit: config.c_cls_lim,
            ..ClauseDB::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        match e {
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
                self.watcher.push(self.watcher[0].empty_copy());
                // for positive literal
                self.bin_watcher.push(Vec::new());
                self.watcher.push(self.watcher[0].empty_copy());
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
    fn watcher_list(&self, l: Lit) -> &WatchList {
        &self.watcher[l]
    }
    #[inline]
    fn bin_watcher_lists(&self) -> &[Vec<Watch>] {
        &self.bin_watcher
    }
    #[inline]
    fn watcher_lists_mut(&mut self) -> &mut [WatchList] {
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
                        activity: c.reward,
                        blocker: NULL_LIT,
                        c: cid,
                    });
                    if c.is(Flag::LEARNT) {
                        self.num_learnt -= 1;
                    }
                    if !certified.is_empty() && !c.is(Flag::VIV_ASSUMP) {
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
            /*
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
                        activity: c.reward as usize,
                        blocker: NULL_LIT,
                        c: cid,
                    });
                    if c.is(Flag::LEARNT) {
                        self.num_learnt -= 1;
                    }
                    if !certified.is_empty() && !c.is(Flag::VIV_ASSUMP) {
                        let temp = c.lits.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
                        debug_assert!(!temp.is_empty());
                        certified.push((CertifiedRecord::DELETE, temp));
                    }
                    c.lits.clear();
                }
                ws.detach(n);
            }
             */
            let mut remain = ws.empty_copy();
            for w in ws.drain() {
                let cid = w.c;
                let c = &mut clause[cid.ordinal as usize];
                if !c.is(Flag::DEAD) {
                    remain.push(w);
                    continue;
                }
                if !c.lits.is_empty() {
                    debug_assert!(c.is(Flag::DEAD));
                    recycled.push(Watch {
                        activity: c.reward,
                        blocker: NULL_LIT,
                        c: cid,
                    });
                    if c.is(Flag::LEARNT) {
                        self.num_learnt -= 1;
                    }
                    if !certified.is_empty() && !c.is(Flag::VIV_ASSUMP) {
                        let temp = c.lits.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
                        debug_assert!(!temp.is_empty());
                        certified.push((CertifiedRecord::DELETE, temp));
                    }
                    c.lits.clear();
                }
            }
            std::mem::swap(ws, &mut remain);
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
        // sort literals
        if level_sort {
            #[cfg(feature = "boundary_check")]
            debug_assert!(1 < vec.len());
            let mut i_max = 1;
            let mut lv_max = 0;
            // seek a literal with max level
            let level = asg.level_ref();
            for (i, l) in vec.iter().enumerate() {
                let vi = l.vi();
                let lv = level[vi];
                if asg.assign(vi).is_some() && lv_max < lv {
                    i_max = i;
                    lv_max = lv;
                }
            }
            vec.swap(1, i_max);
        }
        let rank = {
            // if level_sort {
            // sort literals
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
            if vec.len() <= 2 {
                learnt = false;
                1
            } else {
                let lbd = self.compute_lbd(asg, vec);
                if lbd == 0 {
                    vec.len()
                } else {
                    if self.use_chan_seok && lbd <= self.co_lbd_bound {
                        learnt = false;
                    }
                    lbd
                }
            }
            // } else {
            //    vec.len()
        };
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
            c.rank = rank as u16;
            c.search_from = 2;
        } else {
            cid = ClauseId::from(self.clause.len());
            let mut c = Clause {
                flags: Flag::empty(),
                rank: rank as u16,
                ..Clause::default()
            };
            std::mem::swap(&mut c.lits, vec);
            self.clause.push(c);
        };
        if self.during_vivification {
            self[cid].turn_on(Flag::VIV_ASSUMP);
        }
        let c = &mut self[cid];
        let initial_activity = (0.5 * ACTIVITY_SCALE) as usize;
        c.reward = initial_activity;

        // assert!(0 < c.rank);
        let len2 = c.lits.len() == 2;
        if learnt {
            c.turn_on(Flag::LEARNT);
            c.turn_on(Flag::JUST_USED);

            let lbd2 = c.rank <= 2;
            if len2 {
                self.num_bi_learnt += 1;
            }
            if lbd2 {
                self.num_lbd2 += 1;
            }
            self.num_learnt += 1;
        }
        if len2 {
            self.num_bi_clause += 1;
            self.bin_watcher[!l0].register(initial_activity, l1, cid);
            self.bin_watcher[!l1].register(initial_activity, l0, cid);
        } else {
            self.watcher[!l0].register(initial_activity, l1, cid);
            self.watcher[!l1].register(initial_activity, l0, cid);
        }
        self.num_active += 1;
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
        let nlevels = self.compute_lbd_of(asg, cid);
        let c = &mut self[cid];
        debug_assert!(!c.is(Flag::DEAD), format!("found {} is dead: {}", cid, c));
        if nlevels < c.rank as usize {
            match (c.is(Flag::VIVIFIED2), c.is(Flag::VIVIFIED)) {
                _ if nlevels == 1 || nlevels + 1 < c.rank as usize => {
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
            if !c.is(Flag::JUST_USED) && c.is(Flag::LEARNT) {
                c.turn_on(Flag::JUST_USED);
                // chan_seok_condition is zero if !use_chan_seok
                if nlevels < chan_seok_condition {
                    c.turn_off(Flag::LEARNT);
                    c.rank = nlevels as u16;
                    self.num_learnt -= 1;
                    return true;
                }
            }
        }
        c.rank = nlevels as u16;
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
    fn check_and_reduce<A>(&mut self, asg: &mut A, nc: usize, average: f64) -> bool
    where
        A: AssignIF,
    {
        if !self.reducable || 0 == self.num_learnt {
            return false;
        }
        let go = if self.use_chan_seok {
            self.first_reduction < self.num_learnt
        } else {
            self.reduction_coeff * self.next_reduction <= nc
        };
        if go {
            self.reduction_coeff = ((nc as f64) / (self.next_reduction as f64)) as usize + 1;
            self.reduce(asg, average as u16);
            self.num_reduction += 1;
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
        (*c).turn_on(Flag::JUST_USED);
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
                self.watcher[!p].detach_with(cid);
                self.watcher[!r].detach_with(cid);
                self.bin_watcher[!q].register(0, r, cid);
                self.bin_watcher[!r].register(0, q, cid);
            } else {
                self.watcher[!p].detach_with(cid);
                self.watcher[!q].register(0, r, cid);
                self.watcher[!r].update_blocker(cid, q);
            }
        } else {
            lits.delete_unstable(|&x| x == p);
            if 2 == lits.len() {
                let q = lits[0];
                let r = lits[1];
                self.watcher[!q].detach_with(cid);
                self.watcher[!r].detach_with(cid);
                self.bin_watcher[!q].register(0, r, cid);
                self.bin_watcher[!r].register(0, q, cid);
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
    fn reduce<A>(&mut self, asg: &mut A, _average: u16)
    where
        A: AssignIF,
    {
        struct Record {
            val: i64,
            cid: usize,
        }
        let ClauseDB {
            ref mut clause,
            ref mut touched,
            ..
        } = self;
        self.next_reduction += self.inc_step;
        let steps = asg.exports().0 - self.last_reduction;
        self.last_reduction += steps;
        let mut perm = Vec::with_capacity(clause.len());
        let mut to_remove = 0;
        let mut _ema_lbd = Ema::new(2000);
        let mut _ema_mva = Ema::new(2000);
        let scale = 64.0; //  if self.use_chan_seok { 0.0 } else { 1.8 };
        for (i, c) in clause.iter_mut().enumerate().skip(1) {
            if c.is(Flag::LEARNT) {
                to_remove += 1;
                let used = c.is(Flag::JUST_USED);
                let cid = ClauseId::from(i);
                if !c.is(Flag::DEAD) && !asg.locked(c, cid) && !used {
                    let mva = c.max_var_activity(asg); // .sqrt();
                    c.set_activity(mva);
                    // ema_mva.update(mva);
                    // ema_lbd.update(c.rank as f64);

                    perm.push(Record {
                        val: (-268_435_456.0 * (mva + scale / (c.rank as f64))) as i64,
                        cid: i,
                    });
                }
                if used {
                    c.turn_off(Flag::JUST_USED)
                }
            }
        }
        /*
        println!("N {:>8}: lbd {:>8.5} => index {:8.5}, mva {:>8.5}",
                 to_remove,
                 ema_lbd.get(),
                 scale / ema_lbd.get() - 1.0 / (ema_lbd.get() + 1.0),
                 ema_mva.get(),
        );
        */
        to_remove /= 2;
        if perm.is_empty() || perm.len() <= to_remove.max(self.inc_step) {
            return;
        }
        perm.sort_by_key(|r| r.val);
        if !self.use_chan_seok {
            if clause[perm[perm.len() / 2].cid].rank <= 3 {
                self.next_reduction += self.extra_inc;
            }
            if clause[perm[0].cid].rank <= 5 {
                self.next_reduction += self.extra_inc;
            };
        }
        /*
        perm.retain(|i| {
            let c = &mut clause[*i];
            let result = c.rank < average;
            if !result {
                c.kill(touched);
            }
            result
        });
        */
        // let mut len = perm.len();
        //if keep < len {
        //    for i in (0..len).rev() {
        //        let c = &mut clause[perm[i]];
        //        if 2 < c.rank {
        //            c.kill(touched);
        //            if keep == len {
        //                break;
        //            }
        //            len -= 1;
        //        }
        //    }
        //}
        // for i in &perm[keep..] {
        //     let c = &mut clause[*i];
        //     if 2 < c.rank {
        //         c.kill(touched);
        //     }
        // }
        let target = perm.len() - to_remove;
        /*
        for i in &perm[0..target] {
            let c = &mut clause[*i];
            if average < c.rank {
                c.kill(touched);
            }
        }
        */
        for i in &perm[target..] {
            let c = &mut clause[i.cid];
            if 2 < c.rank {
                c.kill(touched);
            }
        }
        // debug_assert!(perm[0..target].iter().all(|cid| !clause[*cid].is(Flag::DEAD)));
        self.garbage_collect();
    }
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
    pub fn activity(&mut self) -> f64 {
        (self.reward as f64) / ACTIVITY_SCALE
    }
    pub fn set_activity(&mut self, val: f64) {
        self.reward = (val * ACTIVITY_SCALE) as usize;
    }
    pub fn max_var_activity<A>(&mut self, asg: &mut A) -> f64
    where
        A: AssignIF,
    {
        let mut act: f64 = 0.0;
        for l in self.lits.iter() {
            let tmp = asg.activity(l.vi());
            if act < tmp {
                act = tmp;
            }
        }
        act
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

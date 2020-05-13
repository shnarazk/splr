use {
    super::{CertifiedRecord, Clause, ClauseDB, ClauseId, WatchDBIF, LBDIF},
    crate::{
        assign::AssignIF,
        processor::EliminateIF,
        state::{SearchStrategy, State},
        types::*,
    },
    std::{
        cmp::Ordering,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::{Iter, IterMut},
    },
};

const ACTIVITY_MAX: f64 = 1e308;

/// API for clause management like `reduce`, `simplify`, `new_clause`, and so on.
pub trait ClauseDBIF:
    IndexMut<ClauseId, Output = Clause> + Export<(usize, usize, usize, usize, usize, usize)>
{
    /// return the length of `clause`.
    fn len(&self) -> usize;
    /// return true if it's empty.
    fn is_empty(&self) -> bool;
    /// return an iterator.
    fn iter(&self) -> Iter<'_, Clause>;
    /// return a mutable iterator.
    fn iter_mut(&mut self) -> IterMut<'_, Clause>;
    /// return a watcher list
    fn watcher_list(&self, l: Lit) -> &[Watch];
    /// return the list of watch lists
    fn watcher_lists_mut(&mut self) -> &mut [Vec<Watch>];
    /// unregister a clause `cid` from clause database and make the clause dead.
    fn detach(&mut self, cid: ClauseId);
    /// check a condition to reduce.
    /// * return `true` if reduction is done.
    /// * Otherwise return `false`.
    ///
    /// # CAVEAT
    /// *precondition*: decision level == 0.
    fn check_and_reduce<A>(&mut self, asg: &A, nc: usize) -> bool
    where
        A: AssignIF;
    fn reset(&mut self);
    /// delete *dead* clauses from database, which are made by:
    /// * `reduce`
    /// * `simplify`
    /// * `kill`
    fn garbage_collect(&mut self);
    /// allocate a new clause and return its id.
    /// * If `level_sort` is on, register `v` as a learnt after sorting based on assign level.
    /// * Otherwise, register `v` as a permanent clause, which rank is zero.
    fn new_clause<A>(
        &mut self,
        asg: &mut A,
        v: &mut [Lit],
        learnt: bool,
        level_sort: bool,
    ) -> ClauseId
    where
        A: AssignIF;
    /// check and convert a learnt clause to permanent if needed.
    fn convert_to_permanent<A>(&mut self, asg: &mut A, cid: ClauseId) -> bool
    where
        A: AssignIF;
    /// return the number of alive clauses in the database. Or return the database size if `active` is `false`.
    fn count(&self, alive: bool) -> usize;
    /// return the number of clauses which satisfy given flags and aren't DEAD.
    fn countf(&self, mask: Flag) -> usize;
    /// record a clause to unsat certification.
    fn certificate_add(&mut self, vec: &[Lit]);
    /// record a deleted clause to unsat certification.
    fn certificate_delete(&mut self, vec: &[Lit]);
    /// delete satisfied clauses at decision level zero.
    fn eliminate_satisfied_clauses<A, E>(&mut self, asg: &mut A, elim: &mut E, occur: bool)
    where
        A: AssignIF,
        E: EliminateIF;
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
    fn stock(&mut self, cid: ClauseId);
}

impl Default for ClauseDB {
    fn default() -> ClauseDB {
        ClauseDB {
            clause: Vec::new(),
            watcher: Vec::new(),
            certified: Vec::new(),
            soft_limit: 0, // 248_000_000
            use_chan_seok: false,
            co_lbd_bound: 5,
            // lbd_frozen_clause: 30,
            activity_inc: 1.0,
            activity_decay: 0.999,
            touched: Vec::new(),
            lbd_temp: Vec::new(),
            num_lbd_update: 0,
            inc_step: 300,
            extra_inc: 1000,
            first_reduction: 1000,
            next_reduction: 1000,
            reducable: true,
            reduction_coeff: 1,
            num_active: 0,
            num_bi_clause: 0,
            num_bi_learnt: 0,
            num_lbd2: 0,
            num_learnt: 0,
            num_reduction: 0,
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
    type Inc = ();
    fn activity(&mut self, ci: Self::Ix) -> f64 {
        self[ci].reward
    }
    fn bump_activity(&mut self, cid: Self::Ix, _: Self::Inc) {
        let c = &mut self.clause[cid.ordinal as usize];
        let a = c.reward + self.activity_inc;
        c.reward = a;
        if ACTIVITY_MAX < a {
            let scale = 1.0 / self.activity_inc;
            for c in &mut self.clause[1..] {
                if c.is(Flag::LEARNT) {
                    c.reward *= scale;
                }
            }
            self.activity_inc *= scale;
        }
    }
    fn scale_activity(&mut self) {
        self.activity_inc /= self.activity_decay;
    }
}

impl Instantiate for ClauseDB {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> ClauseDB {
        let nv = cnf.num_of_variables;
        let nc = cnf.num_of_clauses;
        let mut clause = Vec::with_capacity(1 + nc);
        clause.push(Clause::default());
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        let mut touched = Vec::with_capacity(2 * (nv + 1));
        for _ in 0..2 * (nv + 1) {
            watcher.push(Vec::new());
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
            watcher,
            certified,
            reducable: config.use_reduce(),
            soft_limit: config.clause_limit,
            ..ClauseDB::default()
        }
    }
    /// # PRECONDITION
    /// decision level must be 0 if `state.strategy.1` == `state[Stat::Conflict]`
    fn adapt_to(&mut self, state: &State, num_conflict: usize) {
        match state.strategy {
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
            (SearchStrategy::HighSuccesive, _) => {
                self.co_lbd_bound = 3;
                self.first_reduction = 30000;
                self.use_chan_seok = true;
                // This call requires 'decision level == 0'.
                self.make_permanent(false);
            }
            (SearchStrategy::LowSuccesive, _) => (),
            (SearchStrategy::ManyGlues, _) => (),
        }
    }
    fn reinitialize(&mut self) {}
}

impl Export<(usize, usize, usize, usize, usize, usize)> for ClauseDB {
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
    fn watcher_lists_mut(&mut self) -> &mut [Vec<Watch>] {
        &mut self.watcher
    }
    fn garbage_collect(&mut self) {
        // debug_assert!(self.check_liveness1());
        let ClauseDB {
            ref mut watcher,
            ref mut clause,
            ref mut touched,
            ref mut certified,
            ..
        } = self;
        debug_assert_eq!(usize::from(!NULL_LIT), 1);
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
                        binary: c.lits.len() == 2,
                    });
                    if c.is(Flag::LEARNT) {
                        self.num_learnt -= 1;
                    }
                    if !certified.is_empty() {
                        let temp = c.lits.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
                        certified.push((CertifiedRecord::ADD, temp));
                    }
                    c.lits.clear();
                }
                ws.detach(n);
            }
        }
        self.num_active = self.clause.len() - recycled.len();
        // debug_assert!(self.check_liveness2());
    }
    fn new_clause<A>(
        &mut self,
        asg: &mut A,
        vec: &mut [Lit],
        mut learnt: bool,
        level_sort: bool,
    ) -> ClauseId
    where
        A: AssignIF,
    {
        let reward = self.activity_inc;
        let rank = if level_sort {
            if !self.certified.is_empty() {
                let temp = vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
                self.certified.push((CertifiedRecord::ADD, temp));
            }
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
            if vec.len() <= 2 {
                learnt = false;
                0
            } else {
                let lbd = self.compute_lbd(asg, vec);
                if self.use_chan_seok && lbd <= self.co_lbd_bound {
                    learnt = false;
                    0
                } else {
                    lbd
                }
            }
        } else {
            0
        };
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
            c.lits.clear();
            for l in vec {
                c.lits.push(*l);
            }
            c.rank = rank;
            c.reward = reward;
            c.search_from = 1;
        } else {
            let lits = Vec::from(vec);
            cid = ClauseId::from(self.clause.len());
            let c = Clause {
                flags: Flag::empty(),
                lits,
                rank,
                reward,
                ..Clause::default()
            };
            self.clause.push(c);
        };
        let c = &mut self[cid];
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
        }
        self.watcher[!l0].register(l1, cid, len2);
        self.watcher[!l1].register(l0, cid, len2);
        self.num_active += 1;
        cid
    }
    fn convert_to_permanent<A>(&mut self, asg: &mut A, cid: ClauseId) -> bool
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
        if c.is(Flag::JUST_USED) {
            return false;
        }
        debug_assert!(!c.is(Flag::DEAD), format!("found {} is dead: {}", cid, c));
        if 2 < c.rank {
            c.turn_on(Flag::JUST_USED);
            if nlevels + 1 < c.rank {
                // chan_seok_condition is zero if !use_chan_seok
                if nlevels < chan_seok_condition {
                    c.turn_off(Flag::LEARNT);
                    self.num_learnt -= 1;
                    return true;
                } else {
                    c.rank = nlevels;
                }
            }
        }
        false
    }
    fn count(&self, alive: bool) -> usize {
        if alive {
            self.clause.len() - self.watcher[!NULL_LIT].len() - 1
        } else {
            self.clause.len() - 1
        }
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
    fn check_and_reduce<A>(&mut self, asg: &A, nc: usize) -> bool
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
            self.reduce(asg);
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
        if !self.certified.is_empty() {
            let temp = vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
            self.certified.push((CertifiedRecord::ADD, temp));
        }
    }
    fn certificate_delete(&mut self, vec: &[Lit]) {
        if !self.certified.is_empty() {
            let temp = vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
            self.certified.push((CertifiedRecord::DELETE, temp));
        }
    }
    fn eliminate_satisfied_clauses<A, E>(&mut self, asg: &mut A, elim: &mut E, update_occur: bool)
    where
        A: AssignIF,
        E: EliminateIF,
    {
        for (cid, c) in &mut self.clause.iter_mut().enumerate().skip(1) {
            if !c.is(Flag::DEAD) && asg.satisfies(&c.lits) {
                c.kill(&mut self.touched);
                if elim.is_running() {
                    if update_occur {
                        elim.remove_cid_occur(asg, ClauseId::from(cid), c);
                    }
                    for l in &c.lits {
                        elim.enqueue_var(asg, l.vi(), true);
                    }
                }
            }
        }
        self.garbage_collect();
    }
    fn touch_var(&mut self, vi: VarId) {
        self.touched[Lit::from_assign(vi, true)] = true;
        self.touched[Lit::from_assign(vi, false)] = true;
    }
    fn check_size(&self) -> Result<bool, SolverError> {
        if self.soft_limit == 0 || self.count(false) <= self.soft_limit {
            Ok(0 == self.soft_limit || 4 * self.count(true) < 3 * self.soft_limit)
        } else {
            Err(SolverError::OutOfMemory)
        }
    }
    fn validate(&self, model: &[Option<bool>], strict: bool) -> Option<ClauseId> {
        for (i, c) in self.clause.iter().enumerate().skip(1) {
            if c.is(Flag::DEAD) || (strict && c.is(Flag::LEARNT)) {
                continue;
            }
            match c.valuate(model) {
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
        (*c).search_from = 1;
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
            let len = lits.len();
            let bin = len == 2;
            self.watcher[!p].detach_with(cid);
            self.watcher[!q].register(r, cid, bin);
            if bin {
                // update another bocker
                self.watcher[!r].update_blocker(cid, q, true);
            }
        } else {
            lits.delete_unstable(|&x| x == p);
            if lits.len() == 2 {
                // update another bocker
                let q = lits[0];
                let r = lits[1];
                self.watcher[!q].update_blocker(cid, r, true);
                self.watcher[!r].update_blocker(cid, q, true);
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
        for w in &self.watcher[!l0] {
            let c = &self.clause[w.c.ordinal as usize];
            if c.len() != 2 {
                continue;
            }
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
    fn stock(&mut self, cid: ClauseId) {
        self.eliminated_permanent
            .push(self.clause[cid.ordinal as usize].lits.clone());
    }
}

impl ClauseDB {
    /// halve the number of 'learnt' or *removable* clauses.
    fn reduce<A>(&mut self, asg: &A)
    where
        A: AssignIF,
    {
        let ClauseDB {
            ref mut clause,
            ref mut touched,
            ..
        } = self;
        self.next_reduction += self.inc_step;
        let mut perm = Vec::with_capacity(clause.len());
        for (i, c) in clause.iter_mut().enumerate().skip(1) {
            let used = c.is(Flag::JUST_USED);
            if c.is(Flag::LEARNT) && !c.is(Flag::DEAD) && !asg.locked(c, ClauseId::from(i)) && !used
            {
                perm.push(i);
            }
            if used {
                c.turn_off(Flag::JUST_USED)
            }
        }
        if perm.is_empty() {
            return;
        }
        let keep = perm.len() / 2;
        if self.use_chan_seok {
            perm.sort_by(|&a, &b| clause[a].cmp_activity(&clause[b]));
        } else {
            perm.sort_by(|&a, &b| clause[a].cmp(&clause[b]));
            if clause[perm[keep]].rank <= 3 {
                self.next_reduction += self.extra_inc;
            }
            if clause[perm[0]].rank <= 5 {
                self.next_reduction += self.extra_inc;
            };
        }
        for i in &perm[keep..] {
            let c = &mut clause[*i];
            if 2 < c.rank {
                c.kill(touched);
            }
        }
        debug_assert!(perm[0..keep].iter().all(|cid| !clause[*cid].is(Flag::DEAD)));
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
            if c.rank <= self.co_lbd_bound {
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
    #[allow(clippy::comparison_chain)]
    fn cmp_activity(&self, other: &Clause) -> Ordering {
        if self.reward > other.reward {
            Ordering::Less
        } else if other.reward > self.reward {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
    /// make a clause *dead*; the clause still exists in clause database as a garbage.
    fn kill(&mut self, touched: &mut [bool]) {
        self.turn_on(Flag::DEAD);
        debug_assert!(1 < usize::from(self.lits[0]) && 1 < usize::from(self.lits[1]));
        touched[!self.lits[0]] = true;
        touched[!self.lits[1]] = true;
    }
    fn valuate(&self, model: &[Option<bool>]) -> Option<bool> {
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

/// Crate `eliminator` implments clause subsumption and var elimination.
use {
    crate::{
        clause::ClauseDBIF,
        propagator::PropagatorIF,
        state::{State, StateIF},
        types::*,
        var::{VarDBIF, VarRewardIF, LBDIF},
    },
    std::{fmt, slice::Iter},
    std::{
        ops::{Index, IndexMut, Range, RangeFrom},
        sync::{
            atomic::{AtomicBool, Ordering},
            Arc,
        },
        thread,
        time::Duration,
    },
};

/// API for Eliminator like `activate`, `stop`, `eliminate` and so on.
///```
/// use crate::{splr::config::Config, splr::types::*};
/// use crate::splr::eliminator::{Eliminator, EliminatorIF};
/// use crate::splr::solver::Solver;

/// let mut s = Solver::instantiate(&Config::default(), &CNFDescription::default());
/// let elim = &mut s.elim;
/// assert_eq!(elim.is_running(), false);
/// elim.activate();
/// // At this point, the `elim` is in `ready` mode, not `running`.
/// assert_eq!(elim.is_running(), false);
/// assert_eq!(elim.simplify(&mut s.asgs, &mut s.cdb, &mut s.state, &mut s.vdb), Ok(()));
///```
pub trait EliminatorIF {
    /// set eliminator's mode to **ready**.
    fn activate(&mut self);
    /// set eliminator's mode to **dormant**.
    fn stop<C, V>(&mut self, cdb: &mut C, vdb: &mut V)
    where
        C: ClauseDBIF,
        V: VarDBIF;
    /// check if the eliminator is running.
    fn is_running(&self) -> bool;
    /// rebuild occur lists.
    fn prepare<C, V>(&mut self, cdb: &mut C, vdb: &mut V, force: bool)
    where
        C: ClauseDBIF,
        V: VarDBIF;
    /// enqueue a var into eliminator's var queue.
    fn enqueue_var<V>(&mut self, vdb: &mut V, vi: VarId, upword: bool)
    where
        V: VarDBIF;
    /// simplify database by:
    /// * removing satisfiable clauses
    /// * calling exhaustive simplifier that tries **clause subsumption** and **variable elimination**.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn simplify<A, C, V>(
        &mut self,
        asgs: &mut A,
        cdb: &mut C,
        state: &mut State,
        vdb: &mut V,
    ) -> MaybeInconsistent
    where
        A: PropagatorIF,
        C: ClauseDBIF,
        V: VarDBIF + VarRewardIF + LBDIF;
    /// inject assignments for eliminated vars.
    fn extend_model<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF;
    /// register a clause id to all corresponding occur lists.
    fn add_cid_occur<V>(&mut self, vdb: &mut V, cid: ClauseId, c: &mut Clause, enqueue: bool)
    where
        V: VarDBIF;
    /// remove a clause id from all corresponding occur lists.
    fn remove_cid_occur<V>(&mut self, vdb: &mut V, cid: ClauseId, c: &mut Clause)
    where
        V: VarDBIF;
    /// return the order of vars based on their occurrences
    fn sorted_iterator(&self) -> Iter<'_, usize>;
    /// return vi's stats
    fn stats(&self, vi: VarId) -> (usize, usize);
}

/// API for getting stats about Eliminator's internal data.
pub trait EliminatorStatIF {
    fn stats(&self) -> (usize, usize);
}

#[derive(Eq, Debug, PartialEq)]
enum EliminatorMode {
    Deactive,
    Waiting,
    Running,
}

/// Mapping from Literal to Clauses.
#[derive(Debug)]
pub struct LitOccurs {
    pos_occurs: Vec<ClauseId>,
    neg_occurs: Vec<ClauseId>,
}

impl Default for LitOccurs {
    fn default() -> LitOccurs {
        LitOccurs {
            pos_occurs: Vec::new(),
            neg_occurs: Vec::new(),
        }
    }
}

impl Export<(usize, usize)> for Eliminator {
    /// exports:
    ///  1. the number of full eliminations
    ///  1. the number of satisfied clause eliminations
    ///
    ///```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use crate::splr::eliminator::Eliminator;
    /// let elim = Eliminator::instantiate(&Config::default(), &CNFDescription::default());
    /// let (elim_num_full_elimination, elim_num_sat_elimination) = elim.exports();
    ///```
    #[inline]
    fn exports(&self) -> (usize, usize) {
        (self.num_full_elimination, self.num_sat_elimination)
    }
}

impl LitOccurs {
    /// return a new vector of $n$ `LitOccurs`s.
    fn new(n: usize) -> Vec<LitOccurs> {
        let mut vec = Vec::with_capacity(n + 1);
        for _ in 0..=n {
            vec.push(LitOccurs::default());
        }
        vec
    }
    fn clear(&mut self) {
        self.pos_occurs.clear();
        self.neg_occurs.clear();
    }
}

/// Literal eliminator
#[derive(Debug)]
pub struct Eliminator {
    pub enable: bool,
    mode: EliminatorMode,
    clause_queue: Vec<ClauseId>,
    var_queue: VarOccHeap,
    bwdsub_assigns: usize,
    elim_clauses: Vec<Lit>,
    /// 0 for no limit
    /// Stop elimination if a generated resolvent is larger than this
    /// 0 means no limit.
    pub eliminate_combination_limit: usize,
    /// Stop elimination if the increase of clauses is over this
    pub eliminate_grow_limit: usize,
    /// A criteria by the product's of its positive occurrences and negative ones
    pub eliminate_occurrence_limit: usize,
    /// Stop subsumption if the size of a clause is over this
    pub subsume_literal_limit: usize,
    /// var
    var: Vec<LitOccurs>,
    num_full_elimination: usize,
    num_sat_elimination: usize,
}

impl Default for Eliminator {
    fn default() -> Eliminator {
        Eliminator {
            enable: true,
            mode: EliminatorMode::Deactive,
            var_queue: VarOccHeap::new(0, 0),
            clause_queue: Vec::new(),
            bwdsub_assigns: 0,
            elim_clauses: Vec::new(),
            eliminate_combination_limit: 80,
            eliminate_grow_limit: 0, // 64
            eliminate_occurrence_limit: 800,
            subsume_literal_limit: 100,
            var: Vec::new(),
            num_full_elimination: 0,
            num_sat_elimination: 0,
        }
    }
}

impl Index<VarId> for Eliminator {
    type Output = LitOccurs;
    #[inline]
    fn index(&self, i: VarId) -> &Self::Output {
        unsafe { self.var.get_unchecked(i) }
    }
}

impl IndexMut<VarId> for Eliminator {
    #[inline]
    fn index_mut(&mut self, i: VarId) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(i) }
    }
}

impl Index<&VarId> for Eliminator {
    type Output = LitOccurs;
    #[inline]
    fn index(&self, i: &VarId) -> &Self::Output {
        unsafe { self.var.get_unchecked(*i) }
    }
}

impl IndexMut<&VarId> for Eliminator {
    #[inline]
    fn index_mut(&mut self, i: &VarId) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(*i) }
    }
}

impl Index<Lit> for Eliminator {
    type Output = LitOccurs;
    #[inline]
    fn index(&self, l: Lit) -> &Self::Output {
        unsafe { self.var.get_unchecked(l.vi()) }
    }
}

impl IndexMut<Lit> for Eliminator {
    #[inline]
    fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(l.vi()) }
    }
}

impl Index<&Lit> for Eliminator {
    type Output = LitOccurs;
    #[inline]
    fn index(&self, l: &Lit) -> &Self::Output {
        unsafe { self.var.get_unchecked(l.vi()) }
    }
}

impl IndexMut<&Lit> for Eliminator {
    #[inline]
    fn index_mut(&mut self, l: &Lit) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(l.vi()) }
    }
}

impl Index<Range<usize>> for Eliminator {
    type Output = [LitOccurs];
    #[inline]
    fn index(&self, r: Range<usize>) -> &Self::Output {
        &self.var[r]
    }
}

impl Index<RangeFrom<usize>> for Eliminator {
    type Output = [LitOccurs];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &Self::Output {
        unsafe { self.var.get_unchecked(r) }
    }
}

impl IndexMut<Range<usize>> for Eliminator {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(r) }
    }
}

impl IndexMut<RangeFrom<usize>> for Eliminator {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut Self::Output {
        &mut self.var[r]
    }
}

impl Instantiate for Eliminator {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Eliminator {
        let nv = cnf.num_of_variables;
        Eliminator {
            enable: !config.without_elim,
            var_queue: VarOccHeap::new(nv, 0),
            eliminate_grow_limit: config.elim_grw_lim,
            subsume_literal_limit: config.elim_lit_lim,
            var: LitOccurs::new(nv + 1),
            ..Eliminator::default()
        }
    }
}

impl EliminatorIF for Eliminator {
    fn activate(&mut self) {
        debug_assert!(self.mode != EliminatorMode::Running);
        self.mode = EliminatorMode::Waiting;
    }
    fn is_running(&self) -> bool {
        self.mode == EliminatorMode::Running
    }
    // Due to a potential bug of killing clauses and difficulty about
    // synchronization between 'garbage_collect' and clearing occur lists,
    // 'stop' should purge all occur lists to purge any dead clauses for now.
    fn stop<C, V>(&mut self, cdb: &mut C, vdb: &mut V)
    where
        C: ClauseDBIF,
        V: VarDBIF,
    {
        let force: bool = true;
        self.clear_clause_queue(cdb);
        self.clear_var_queue(vdb);
        if force {
            for c in &mut cdb.iter_mut().skip(1) {
                c.turn_off(Flag::OCCUR_LINKED);
            }
            for w in &mut self[1..] {
                w.clear();
            }
        }
        self.mode = EliminatorMode::Deactive;
    }
    fn prepare<C, V>(&mut self, cdb: &mut C, vdb: &mut V, force: bool)
    where
        C: ClauseDBIF,
        V: VarDBIF,
    {
        if self.mode != EliminatorMode::Waiting {
            return;
        }
        self.mode = EliminatorMode::Running;
        for w in &mut self[1..] {
            w.clear();
        }
        for (cid, c) in &mut cdb.iter_mut().enumerate().skip(1) {
            if c.is(Flag::DEAD) || c.is(Flag::OCCUR_LINKED) {
                continue;
            }
            self.add_cid_occur(vdb, ClauseId::from(cid), c, false);
        }
        if force {
            for vi in 1..vdb.len() {
                let v = &vdb[vi];
                if v.is(Flag::ELIMINATED) || v.assign.is_some() {
                    continue;
                }
                self.enqueue_var(vdb, vi, true);
            }
        }
    }
    fn enqueue_var<V>(&mut self, vdb: &mut V, vi: VarId, upward: bool)
    where
        V: VarDBIF,
    {
        if self.mode != EliminatorMode::Running {
            return;
        }
        let v = &mut vdb[vi];
        let w = &mut self[vi];
        if !v.is(Flag::ENQUEUED) && w.activity() < self.eliminate_occurrence_limit {
            v.turn_on(Flag::ENQUEUED);
            self.var_queue.insert(&self.var, vi, upward);
        }
    }
    fn simplify<A, C, V>(
        &mut self,
        asgs: &mut A,
        cdb: &mut C,
        state: &mut State,
        vdb: &mut V,
    ) -> MaybeInconsistent
    where
        A: PropagatorIF,
        C: ClauseDBIF,
        V: VarDBIF + VarRewardIF + LBDIF,
    {
        debug_assert_eq!(asgs.level(), 0);
        // we can reset all the reasons because decision level is zero.
        for v in vdb.iter_mut().skip(1) {
            v.reason = ClauseId::default();
        }
        if self.is_waiting() {
            self.prepare(cdb, vdb, true);
        }
        self.eliminate(asgs, cdb, state, vdb)?;
        self.num_sat_elimination += 1;
        if self.is_running() {
            self.num_full_elimination += 1;
            vdb.reset_lbd(cdb);
            self.stop(cdb, vdb);
        }
        cdb.check_size().map(|_| ())
    }
    fn extend_model<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF,
    {
        if self.elim_clauses.is_empty() {
            return;
        }
        let mut i = self.elim_clauses.len() - 1;
        let mut width;
        'next: loop {
            width = usize::from(self.elim_clauses[i]);
            if width == 0 && i == 0 {
                break;
            }
            i -= 1;
            loop {
                if width <= 1 {
                    break;
                }
                let l = self.elim_clauses[i];
                // let model_value = match model[l.vi() - 1] {
                //     x if x == l.to_i32() => Some(true),
                //     x if -x == l.to_i32() => Some(false),
                //     _ => None,
                // };
                // if model_value != Some(false) {
                if !Lit::from(&vdb[l]) != l {
                    if i < width {
                        break 'next;
                    }
                    i -= width;
                    continue 'next;
                }
                width -= 1;
                i -= 1;
            }
            debug_assert!(width == 1);
            let l = self.elim_clauses[i];
            // debug_assert!(model[l.vi() - 1] != l.negate().int());
            vdb[l].assign = Some(bool::from(l));
            if i < width {
                break;
            }
            i -= width;
        }
    }
    fn add_cid_occur<V>(&mut self, vdb: &mut V, cid: ClauseId, c: &mut Clause, enqueue: bool)
    where
        V: VarDBIF,
    {
        if self.mode != EliminatorMode::Running || c.is(Flag::OCCUR_LINKED) {
            return;
        }
        for l in &c.lits {
            let v = &mut vdb[l.vi()];
            let w = &mut self[l.vi()];
            v.turn_on(Flag::TOUCHED);
            if !v.is(Flag::ELIMINATED) {
                if bool::from(*l) {
                    debug_assert!(
                        !w.pos_occurs.contains(&cid),
                        format!("{} {:?} {}", cid, vec2int(&c.lits), v.index,)
                    );
                    w.pos_occurs.push(cid);
                } else {
                    debug_assert!(
                        !w.neg_occurs.contains(&cid),
                        format!("{} {:?} {}", cid, vec2int(&c.lits), v.index,)
                    );
                    w.neg_occurs.push(cid);
                }
                self.enqueue_var(vdb, l.vi(), false);
            }
        }
        c.turn_on(Flag::OCCUR_LINKED);
        if enqueue {
            self.enqueue_clause(cid, c);
        }
    }
    fn remove_cid_occur<V>(&mut self, vdb: &mut V, cid: ClauseId, c: &mut Clause)
    where
        V: VarDBIF,
    {
        debug_assert!(self.mode == EliminatorMode::Running);
        debug_assert!(!cid.is_lifted_lit());
        c.turn_off(Flag::OCCUR_LINKED);
        debug_assert!(c.is(Flag::DEAD));
        for l in &c.lits {
            if vdb[l.vi()].assign.is_none() {
                self.remove_lit_occur(vdb, *l, cid);
                self.enqueue_var(vdb, l.vi(), true);
            }
        }
    }
    fn sorted_iterator(&self) -> Iter<'_, usize> {
        self.var_queue.heap[1..].iter()
    }
    fn stats(&self, vi: VarId) -> (usize, usize) {
        let w = &self[vi];
        (w.pos_occurs.len(), w.neg_occurs.len())
    }
}

impl Eliminator {
    /// check if the eliminator is active and waits for next `eliminate`.
    fn is_waiting(&self) -> bool {
        self.mode == EliminatorMode::Waiting
    }

    /// returns false if solver is inconsistent
    /// - calls `clause_queue.pop`
    fn backward_subsumption_check<A, C, V>(
        &mut self,
        asgs: &mut A,
        cdb: &mut C,
        vdb: &mut V,
        timedout: &Arc<AtomicBool>,
    ) -> MaybeInconsistent
    where
        A: PropagatorIF,
        C: ClauseDBIF,
        V: VarDBIF + VarRewardIF,
    {
        debug_assert_eq!(asgs.level(), 0);
        while !self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len() {
            // Check top-level assignments by creating a dummy clause and placing it in the queue:
            if self.clause_queue.is_empty() && self.bwdsub_assigns < asgs.len() {
                let c = ClauseId::from(asgs[self.bwdsub_assigns]);
                self.clause_queue.push(c);
                self.bwdsub_assigns += 1;
            }
            let cid = match self.clause_queue.pop() {
                Some(x) => x,
                None => ClauseId::default(),
            };
            // assert_ne!(cid, 0);
            if timedout.load(Ordering::Acquire) {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(vdb);
                continue;
            }
            let best = if cid.is_lifted_lit() {
                Lit::from(cid).vi()
            } else {
                let mut tmp = cdb.count(true);
                let c = &mut cdb[cid];
                c.turn_off(Flag::ENQUEUED);
                let lits = &c.lits;
                if c.is(Flag::DEAD) || self.subsume_literal_limit < lits.len() {
                    continue;
                }
                // if c is subsumed by c', both of c and c' are included in the occurs of all literals of c
                // so searching the shortest occurs is most efficient.
                let mut b = 0;
                for l in lits {
                    let v = &vdb[l.vi()];
                    let w = &self[l.vi()];
                    if v.assign.is_some() {
                        continue;
                    }
                    let nsum = if bool::from(*l) {
                        w.neg_occurs.len()
                    } else {
                        w.pos_occurs.len()
                    };
                    if !v.is(Flag::ELIMINATED) && nsum < tmp {
                        b = l.vi();
                        tmp = nsum;
                    }
                }
                b
            };
            if best == 0 || vdb[best].is(Flag::ELIMINATED) {
                continue;
            }
            unsafe {
                for cs in &[
                    &mut self[best].pos_occurs as *mut Vec<ClauseId>,
                    &mut self[best].neg_occurs as *mut Vec<ClauseId>,
                ] {
                    for did in &**cs {
                        if *did == cid {
                            continue;
                        }
                        let db = &cdb[*did];
                        if !db.is(Flag::DEAD) && db.len() <= self.subsume_literal_limit {
                            try_subsume(asgs, cdb, self, vdb, cid, *did)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
    /// run clause subsumption and variable elimination.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn eliminate<A, C, V>(
        &mut self,
        asgs: &mut A,
        cdb: &mut C,
        state: &mut State,
        vdb: &mut V,
    ) -> MaybeInconsistent
    where
        A: PropagatorIF,
        C: ClauseDBIF,
        V: VarDBIF + VarRewardIF + LBDIF,
    {
        let start = state.elapsed().unwrap_or(0.0);
        loop {
            let na = asgs.len();
            self.eliminate_main(asgs, cdb, state, vdb)?;
            cdb.eliminate_satisfied_clauses(self, vdb, true);
            if na == asgs.len()
                && (!self.is_running()
                    || (0 == self.clause_queue_len() && 0 == self.var_queue_len()))
            {
                break;
            }
            if 0.1 <= state.elapsed().unwrap_or(1.0) - start {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(vdb);
                break;
            }
        }
        Ok(())
    }
    /// do the elimination task
    fn eliminate_main<A, C, V>(
        &mut self,
        asgs: &mut A,
        cdb: &mut C,
        state: &mut State,
        vdb: &mut V,
    ) -> MaybeInconsistent
    where
        A: PropagatorIF,
        C: ClauseDBIF,
        V: VarDBIF + VarRewardIF + LBDIF,
    {
        /// The ratio of time slot for single elimination step.
        /// Since it is measured in millisecond, 1000 means executing elimination
        /// until timed out. 100 means this function can consume 10% of a given time.
        const TIMESLOT_FOR_ELIMINATION: u64 = 50;
        debug_assert!(asgs.level() == 0);
        if self.mode == EliminatorMode::Deactive {
            return Ok(());
        }
        let timedout = Arc::new(AtomicBool::new(false));
        let timedout2 = timedout.clone();
        let time = TIMESLOT_FOR_ELIMINATION * state.config.timeout as u64;
        thread::spawn(move || {
            thread::sleep(Duration::from_millis(time));
            timedout2.store(true, Ordering::Release);
        });
        while self.bwdsub_assigns < asgs.len()
            || !self.var_queue.is_empty()
            || !self.clause_queue.is_empty()
        {
            if !self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len() {
                self.backward_subsumption_check(asgs, cdb, vdb, &timedout)?;
            }
            while let Some(vi) = self.var_queue.select_var(&self.var, vdb) {
                // timedout = cvar.wait(timedout).unwrap();
                let v = &mut vdb[vi];
                v.turn_off(Flag::ENQUEUED);
                if !v.is(Flag::ELIMINATED) && v.assign.is_none() {
                    eliminate_var(asgs, cdb, self, state, vdb, vi, &timedout)?;
                }
            }
            self.backward_subsumption_check(asgs, cdb, vdb, &timedout)?;
            debug_assert!(self.clause_queue.is_empty());
            cdb.garbage_collect();
            if asgs.propagate(cdb, vdb) != ClauseId::default() {
                return Err(SolverError::Inconsistent);
            }
            cdb.eliminate_satisfied_clauses(self, vdb, true);
            if timedout.load(Ordering::Acquire) {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(vdb);
            }
        }
        Ok(())
    }
    /// remove a clause id from literal's occur list.
    fn remove_lit_occur<V>(&mut self, vdb: &mut V, l: Lit, cid: ClauseId)
    where
        V: VarDBIF,
    {
        let w = &mut self[l.vi()];
        if bool::from(l) {
            debug_assert_eq!(w.pos_occurs.iter().filter(|&c| *c == cid).count(), 1);
            w.pos_occurs.delete_unstable(|&c| c == cid);
            debug_assert!(!w.pos_occurs.contains(&cid));
        } else {
            debug_assert_eq!(w.neg_occurs.iter().filter(|&c| *c == cid).count(), 1);
            w.neg_occurs.delete_unstable(|&c| c == cid);
            debug_assert!(!w.neg_occurs.contains(&cid));
        }
        self.enqueue_var(vdb, l.vi(), true);
    }

    ///
    /// clause queue operations
    ///

    /// enqueue a clause into eliminator's clause queue.
    fn enqueue_clause(&mut self, cid: ClauseId, c: &mut Clause) {
        if self.mode != EliminatorMode::Running || c.is(Flag::ENQUEUED) {
            return;
        }
        self.clause_queue.push(cid);
        c.turn_on(Flag::ENQUEUED);
    }
    /// clear eliminator's clause queue.
    fn clear_clause_queue<C>(&mut self, cdb: &mut C)
    where
        C: ClauseDBIF,
    {
        for cid in &self.clause_queue {
            cdb[*cid].turn_off(Flag::ENQUEUED);
        }
        self.clause_queue.clear();
    }
    /// return the length of eliminator's clause queue.
    fn clause_queue_len(&self) -> usize {
        self.clause_queue.len()
    }

    ///
    /// var queue operations
    ///

    /// clear eliminator's var queue
    fn clear_var_queue<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF,
    {
        self.var_queue.clear(vdb);
    }
    /// return the length of eliminator's var queue.
    fn var_queue_len(&self) -> usize {
        self.var_queue.len()
    }
}

fn try_subsume<A, C, V>(
    asgs: &mut A,
    cdb: &mut C,
    elim: &mut Eliminator,
    vdb: &mut V,
    cid: ClauseId,
    did: ClauseId,
) -> MaybeInconsistent
where
    A: PropagatorIF,
    C: ClauseDBIF,
    V: VarDBIF + VarRewardIF,
{
    match subsume(cdb, cid, did) {
        Some(NULL_LIT) => {
            // println!("BackSubsC    => {} {} subsumed completely by {} {:#}",
            //          did.fmt(),
            //          *clause!(cdb, cid),
            //          cid.fmt(),
            //          *clause!(cdb, cid),
            // );
            cdb.detach(did);
            elim.remove_cid_occur(vdb, did, &mut cdb[did]);
            if !cdb[did].is(Flag::LEARNT) {
                cdb[cid].turn_off(Flag::LEARNT);
            }
        }
        Some(l) => {
            // println!("BackSubC subsumes {} from {} and {}", l.int(), cid.format(), did.format());
            strengthen_clause(asgs, cdb, elim, vdb, did, !l)?;
            elim.enqueue_var(vdb, l.vi(), true);
        }
        None => {}
    }
    Ok(())
}

/// returns a literal if these clauses can be merged by the literal.
fn subsume<C>(cdb: &mut C, cid: ClauseId, other: ClauseId) -> Option<Lit>
where
    C: ClauseDBIF,
{
    debug_assert!(!other.is_lifted_lit());
    if cid.is_lifted_lit() {
        let l = Lit::from(cid);
        let oh = &cdb[other];
        for lo in &oh.lits {
            if l == !*lo {
                return Some(l);
            }
        }
        return None;
    }
    let mut ret: Lit = NULL_LIT;
    let ch = &cdb[cid];
    let ob = &cdb[other];
    debug_assert!(ob.lits.contains(&ob[0]));
    debug_assert!(ob.lits.contains(&ob[1]));
    'next: for l in &ch.lits {
        for lo in &ob.lits {
            if *l == *lo {
                continue 'next;
            } else if ret == NULL_LIT && *l == !*lo {
                ret = *l;
                continue 'next;
            }
        }
        return None;
    }
    Some(ret)
}

/// Returns:
/// - `(false, -)` if one of the clauses is always satisfied.
/// - `(true, n)` if they are mergeable to a n-literal clause.
fn check_to_merge<C, V>(cdb: &C, vdb: &V, cp: ClauseId, cq: ClauseId, v: VarId) -> (bool, usize)
where
    C: ClauseDBIF,
    V: VarDBIF,
{
    let pqb = &cdb[cp];
    let qpb = &cdb[cq];
    let ps_smallest = pqb.len() < qpb.len();
    let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
    let mut size = pb.lits.len() + 1;
    'next_literal: for l in &qb.lits {
        if vdb[l.vi()].is(Flag::ELIMINATED) {
            continue;
        }
        if l.vi() != v {
            for j in &pb.lits {
                if vdb[j.vi()].is(Flag::ELIMINATED) {
                    continue;
                }
                if j.vi() == l.vi() {
                    if !*j == *l {
                        return (false, size);
                    } else {
                        continue 'next_literal;
                    }
                }
            }
            size += 1;
        }
    }
    (true, size)
}

#[allow(dead_code)]
fn check_eliminator<C>(cdb: &C, elim: &Eliminator, _vdb: &[Var]) -> bool
where
    C: ClauseDBIF,
{
    // clause_queue should be clear.
    // all elements in occur_lists exist.
    // for v in vdb {
    //     for ci in &v.pos_occurs {
    //         let c = clause!(cp, ci);
    //         if c[0] < 2 || c[1] < 2 {
    //             panic!("panic {:#}", c);
    //         }
    //     }
    //     for ci in &v.neg_occurs {
    //         let c = clause!(cp, ci);
    //         if c[0] < 2 || c[1] < 2 {
    //             panic!("panic {:#}", c);
    //         }
    //     }
    // }
    // all clauses are registered in corresponding occur_lists
    for (cid, c) in cdb.iter().enumerate().skip(1) {
        if c.is(Flag::DEAD) {
            continue;
        }
        for l in &c.lits {
            let v = l.vi();
            if bool::from(*l) {
                if !elim[v].pos_occurs.contains(&(ClauseId::from(cid))) {
                    panic!("failed to check {} {:#}", (ClauseId::from(cid)), c);
                }
            } else if !elim[v].neg_occurs.contains(&(ClauseId::from(cid))) {
                panic!("failed to check {} {:#}", (ClauseId::from(cid)), c);
            }
        }
    }
    true
}

/// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
fn merge<C>(cdb: &mut C, cip: ClauseId, ciq: ClauseId, v: VarId, vec: &mut Vec<Lit>) -> usize
where
    C: ClauseDBIF,
{
    vec.clear();
    let pqb = &cdb[cip];
    let qpb = &cdb[ciq];
    let ps_smallest = pqb.len() < qpb.len();
    let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
    // println!(" -  {:?}{:?} & {:?}{:?}", vec2int(&ph.lit),vec2int(&pb.lits),vec2int(&qh.lit),vec2int(&qb.lits));
    'next_literal: for l in &qb.lits {
        if l.vi() != v {
            for j in &pb.lits {
                if j.vi() == l.vi() {
                    if !*j == *l {
                        return 0;
                    } else {
                        continue 'next_literal;
                    }
                }
            }
            vec.push(*l);
        }
    }
    for l in &pb.lits {
        if l.vi() != v {
            vec.push(*l);
        }
    }
    // println!("merge generated {:?} from {} and {} to eliminate {}", vec2int(vec.clone()), p, q, v);
    vec.len()
}

/// removes `l` from clause `cid`
/// - calls `enqueue_clause`
/// - calls `enqueue_var`
fn strengthen_clause<A, C, V>(
    asgs: &mut A,
    cdb: &mut C,
    elim: &mut Eliminator,
    vdb: &mut V,
    cid: ClauseId,
    l: Lit,
) -> MaybeInconsistent
where
    A: PropagatorIF,
    C: ClauseDBIF,
    V: VarDBIF + VarRewardIF,
{
    debug_assert!(!cdb[cid].is(Flag::DEAD));
    debug_assert!(1 < cdb[cid].len());
    cdb.touch_var(l.vi());
    debug_assert_ne!(cid, ClauseId::default());
    if cdb.strengthen(cid, l) {
        // Vaporize the binary clause
        debug_assert!(2 == cdb[cid].len());
        let c0 = cdb[cid][0];
        debug_assert_ne!(c0, l);
        // println!("{} {:?} is removed and its first literal {} is enqueued.", cid.format(), vec2int(&cdb.clause[cid].lits), c0.int());
        cdb.detach(cid);
        elim.remove_cid_occur(vdb, cid, &mut cdb[cid]);
        asgs.assign_at_rootlevel(vdb, c0)
    } else {
        // println!("cid {} drops literal {}", cid.fmt(), l.int());
        debug_assert!(1 < cdb[cid].len());
        elim.enqueue_clause(cid, &mut cdb[cid]);
        elim.remove_lit_occur(vdb, l, cid);
        unsafe {
            let vec = &cdb[cid].lits[..] as *const [Lit];
            cdb.certificate_add(&*vec);
        }
        Ok(())
    }
}

fn make_eliminating_unit_clause(vec: &mut Vec<Lit>, x: Lit) {
    vec.push(x);
    vec.push(Lit::from(1usize));
}

fn make_eliminated_clause<C>(cdb: &mut C, vec: &mut Vec<Lit>, vi: VarId, cid: ClauseId)
where
    C: ClauseDBIF,
{
    let first = vec.len();
    // Copy clause to the vector. Remember the position where the variable 'v' occurs:
    let c = &cdb[cid];
    debug_assert!(!c.is_empty());
    for l in &c.lits {
        vec.push(*l as Lit);
        if l.vi() == vi {
            let index = vec.len() - 1;
            debug_assert_eq!(vec[index], *l);
            debug_assert_eq!(vec[index].vi(), vi);
            // swap the first literal with the 'v'. So that the literal containing 'v' will occur first in the clause.
            vec.swap(index, first);
        }
    }
    // Store the length of the clause last:
    debug_assert_eq!(vec[first].vi(), vi);
    vec.push(Lit::from(c.len()));
    cdb.touch_var(vi);
    // println!("make_eliminated_clause: eliminate({}) clause {:?}", vi, vec2int(&ch.lits));
}

fn eliminate_var<A, C, V>(
    asgs: &mut A,
    cdb: &mut C,
    elim: &mut Eliminator,
    state: &mut State,
    vdb: &mut V,
    vi: VarId,
    timedout: &Arc<AtomicBool>,
) -> MaybeInconsistent
where
    A: PropagatorIF,
    C: ClauseDBIF,
    V: VarDBIF + VarRewardIF + LBDIF,
{
    let v = &mut vdb[vi];
    let w = &mut elim[vi];
    if v.assign.is_some() {
        return Ok(());
    }
    debug_assert!(!v.is(Flag::ELIMINATED));
    // count only alive clauses
    w.pos_occurs.retain(|&c| !cdb[c].is(Flag::DEAD));
    w.neg_occurs.retain(|&c| !cdb[c].is(Flag::DEAD));
    let pos = &w.pos_occurs as *const Vec<ClauseId>;
    let neg = &w.neg_occurs as *const Vec<ClauseId>;
    unsafe {
        if skip_var_elimination(cdb, elim, vdb, &*pos, &*neg, vi) {
            return Ok(());
        }
        // OK, eliminate the literal and build constraints on it.
        state.num_eliminated_vars += 1;
        make_eliminated_clauses(cdb, elim, vi, &*pos, &*neg);
        let vec = &mut state.new_learnt as *mut Vec<Lit>;
        // Produce clauses in cross product:
        for p in &*pos {
            for n in &*neg {
                // println!("eliminator replaces {} with a cross product {:?}", p.fmt(), vec2int(&vec));
                match merge(cdb, *p, *n, vi, &mut *vec) {
                    0 => (),
                    1 => {
                        // println!(
                        //     "eliminate_var: grounds {} from {}{:?} and {}{:?}",
                        //     vec[0].int(),
                        //     p.fmt(),
                        //     vec2int(&clause!(*cp, *p).lits),
                        //     n.fmt(),
                        //     vec2int(&clause!(*cp, *n).lits)
                        // );
                        let lit = (*vec)[0];
                        cdb.certificate_add(&*vec);
                        asgs.assign_at_rootlevel(vdb, lit)?;
                    }
                    _ => {
                        let cid = if cdb[*p].is(Flag::LEARNT) && cdb[*n].is(Flag::LEARNT) {
                            cdb.new_clause(&mut *vec, Some(vdb))
                        } else {
                            cdb.new_clause(&mut *vec, None::<&mut V>)
                        };
                        elim.add_cid_occur(vdb, cid, &mut cdb[cid], true);
                    }
                }
            }
        }
        //
        //## VAR ELIMINATION
        //
        for cid in &*pos {
            debug_assert!(!vdb.locked(&cdb[*cid], *cid));
            cdb.detach(*cid);
            elim.remove_cid_occur(vdb, *cid, &mut cdb[*cid]);
        }
        for cid in &*neg {
            debug_assert!(!vdb.locked(&cdb[*cid], *cid));
            cdb.detach(*cid);
            elim.remove_cid_occur(vdb, *cid, &mut cdb[*cid]);
        }
        elim[vi].clear();
        vdb[vi].turn_on(Flag::ELIMINATED);
        vdb.clear_reward(vi);
        elim.backward_subsumption_check(asgs, cdb, vdb, timedout)
    }
}

/// returns `true` if elimination is impossible.
fn skip_var_elimination<C, V>(
    cdb: &C,
    elim: &mut Eliminator,
    vdb: &V,
    pos: &[ClauseId],
    neg: &[ClauseId],
    v: VarId,
) -> bool
where
    C: ClauseDBIF,
    V: VarDBIF,
{
    // avoid thrashing
    let limit = match cdb.check_size() {
        Ok(true) => elim.eliminate_grow_limit,
        Ok(false) => elim.eliminate_grow_limit / 4,
        Err(_) => return true,
    };
    let clslen = pos.len() + neg.len();
    let mut cnt = 0;
    for c_pos in pos {
        for c_neg in neg {
            let (res, clause_size) = check_to_merge(cdb, vdb, *c_pos, *c_neg, v);
            if res {
                cnt += 1;
                if clslen + limit < cnt
                    || (elim.eliminate_combination_limit != 0
                        && elim.eliminate_combination_limit < clause_size)
                {
                    return true;
                }
            }
        }
    }
    false
}

fn make_eliminated_clauses<C>(
    cdb: &mut C,
    elim: &mut Eliminator,
    v: VarId,
    pos: &[ClauseId],
    neg: &[ClauseId],
) where
    C: ClauseDBIF,
{
    let tmp = &mut elim.elim_clauses;
    if neg.len() < pos.len() {
        for cid in neg {
            debug_assert!(!cdb[*cid].is(Flag::DEAD));
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from_assign(v, true));
    } else {
        for cid in pos {
            debug_assert!(!cdb[*cid].is(Flag::DEAD));
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from_assign(v, false));
    }
}

impl LitOccurs {
    fn activity(&self) -> usize {
        self.pos_occurs.len().min(self.neg_occurs.len())
    }
}

/// Var heap structure based on the number of occurrences
// # Note
// - both fields has a fixed length. Don't use push and pop.
// - `idxs[0]` contains the number of alive elements
//   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Debug)]
pub struct VarOccHeap {
    heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
}

trait VarOrderIF {
    fn new(n: usize, init: usize) -> VarOccHeap;
    fn insert(&mut self, occur: &[LitOccurs], vi: VarId, upword: bool);
    fn clear<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn select_var<V>(&mut self, occur: &[LitOccurs], vdb: &V) -> Option<VarId>
    where
        V: Index<VarId, Output = Var>;
    fn rebuild<V>(&mut self, occur: &[LitOccurs], vdb: &V)
    where
        V: VarDBIF;
}

impl VarOrderIF for VarOccHeap {
    fn new(n: usize, init: usize) -> VarOccHeap {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(n);
        for i in 1..=n {
            heap.push(i);
            idxs.push(i);
        }
        idxs[0] = init;
        VarOccHeap { heap, idxs }
    }
    fn insert(&mut self, occur: &[LitOccurs], vi: VarId, upward: bool) {
        debug_assert!(vi < self.heap.len());
        if self.contains(vi) {
            let i = self.idxs[vi];
            if upward {
                self.percolate_up(occur, i);
            } else {
                self.percolate_down(occur, i);
            }
            return;
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n];
        self.heap.swap(i, n);
        self.idxs.swap(vi, vn);
        debug_assert!(n < self.heap.len());
        self.idxs[0] = n;
        self.percolate_up(occur, n);
    }
    fn clear<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF,
    {
        for v in &mut self.heap[0..self.idxs[0]] {
            vdb[*v].turn_off(Flag::ENQUEUED);
        }
        self.reset()
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
    fn select_var<V>(&mut self, occur: &[LitOccurs], vdb: &V) -> Option<VarId>
    where
        V: Index<VarId, Output = Var>,
    {
        loop {
            let vi = self.get_root(occur);
            if vi == 0 {
                return None;
            }
            if !vdb[vi].is(Flag::ELIMINATED) {
                return Some(vi);
            }
        }
    }
    fn rebuild<V>(&mut self, occur: &[LitOccurs], vdb: &V)
    where
        V: VarDBIF,
    {
        self.reset();
        for v in vdb.iter().skip(1) {
            if v.assign.is_none() && !v.is(Flag::ELIMINATED) {
                self.insert(occur, v.index, true);
            }
        }
    }
}

impl VarOccHeap {
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn reset(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    fn get_root(&mut self, occur: &[LitOccurs]) -> VarId {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        debug_assert!(n < self.heap.len());
        if n == 0 {
            return 0;
        }
        let vn = self.heap[n];
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(occur, 1);
        }
        vs
    }
    fn percolate_up(&mut self, occur: &[LitOccurs], start: usize) {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = occur[vq].activity();
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = occur[vp].activity();
                if ap > aq {
                    // move down the current parent, and make it empty
                    self.heap[q] = vp;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vp] = q;
                    q = p;
                } else {
                    self.heap[q] = vq;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vq] = q;
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, occur: &[LitOccurs], start: usize) {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i];
        let ai = occur[vi].activity();
        loop {
            let l = 2 * i; // left
            if l < n {
                let vl = self.heap[l];
                let al = occur[vl].activity();
                let r = l + 1; // right
                let (target, vc, ac) = if r < n && al > occur[self.heap[r]].activity() {
                    let vr = self.heap[r];
                    (r, vr, occur[vr].activity())
                } else {
                    (l, vl, al)
                };
                if ai > ac {
                    self.heap[i] = vc;
                    self.idxs[vc] = i;
                    i = target;
                } else {
                    self.heap[i] = vi;
                    debug_assert!(vi != 0, "invalid index");
                    self.idxs[vi] = i;
                    return;
                }
            } else {
                self.heap[i] = vi;
                debug_assert!(vi != 0, "invalid index");
                self.idxs[vi] = i;
                return;
            }
        }
    }
    #[allow(dead_code)]
    fn peek(&self) -> VarId {
        self.heap[1]
    }
    #[allow(dead_code)]
    fn remove(&mut self, occur: &[LitOccurs], vs: VarId) {
        let s = self.idxs[vs];
        let n = self.idxs[0];
        if n < s {
            return;
        }
        let vn = self.heap[n];
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(occur, 1);
        }
    }
    #[allow(dead_code)]
    fn check(&self, s: &str) {
        let h = &mut self.heap.clone()[1..];
        let d = &mut self.idxs.clone()[1..];
        h.sort();
        d.sort();
        for i in 0..h.len() {
            if h[i] != i + 1 {
                panic!("heap {} {} {:?}", i, h[i], h);
            }
            if d[i] != i + 1 {
                panic!("idxs {} {} {:?}", i, d[i], d);
            }
        }
        println!(" - pass var_order test at {}", s);
    }
}

impl fmt::Display for VarOccHeap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            " - seek pointer - nth -> var: {:?}\n - var -> nth: {:?}",
            self.heap, self.idxs,
        )
    }
}

#[cfg(test)]
mod tests {
    #![allow(unused_imports)]
    #![allow(unused_variables)]
    #![allow(dead_code)]
    use super::*;
    use crate::{clause::ClauseDB, solver::Solver, var::VarDB};

    macro_rules! mkv {
        ($($x:expr),*) => {
            match &[$($x),*] {
                v => v.iter().map(|x| Lit::from(*x as i32)).collect::<Vec<Lit>>(),
            }
        };
    }

    #[test]
    fn check_occurs() {
        let cfg: Config = Default::default();
        let cnf: CNFDescription = CNFDescription {
            num_of_variables: 10,
            num_of_clauses: 10,
            pathname: "".to_string(),
        };
        let mut s = Solver::instantiate(&cfg, &cnf);

        let c1 = s.cdb.new_clause(&mut mkv![1, 2, 3], None::<&mut VarDB>);
        let c2 = s.cdb.new_clause(&mut mkv![-2, 3, 4], None::<&mut VarDB>);
        let c3 = s.cdb.new_clause(&mut mkv![-2, -3], None::<&mut VarDB>);
        let c4 = s.cdb.new_clause(&mut mkv![1, 2, -3, 9], None::<&mut VarDB>);
        //    {
        //        let vec = [&c2, &c3]; // [&c1, &c2, &c3, &c4];
        //        for x in &vec {
        //            for y in &vec {
        //                println!(
        //                    "{}\tsubsumes\t{}\t=>\t{:?}",
        //                    x,
        //                    y,
        //                    x.subsumes(&y).map(|l| l.int())
        //                );
        //            }
        //        }
        //    }
        //    // s.attach_clause(c1);
        //    s.attach_clause(c2);
        //    s.attach_clause(c3);
        //    // s.attach_clause(c4);
        //    // s.vars.dump("##added");
        //    println!("{:?}", s.eliminator);
        //    s.eliminate();
        //    // s.vars.dump("##eliminated");
        //    println!("{:?}", s.eliminator);
        //    println!("::done");
    }

    fn mk_c(s: &mut Solver, i: usize, v: Vec<i32>) -> ClauseId {
        let mut vec = v.iter().map(|i| Lit::from(*i)).collect::<Vec<Lit>>();
        let cid = s.cdb.new_clause(&mut vec, None::<&mut VarDB>);
        cid
    }
}

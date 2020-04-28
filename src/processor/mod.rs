/// Crate `processor` implements a simplifier: clause subsumption and var elimination.
mod eliminate;
mod heap;
mod subsume;

use {
    self::{eliminate::eliminate_var, heap::VarOrderIF, subsume::try_subsume},
    crate::{
        assign::AssignIF,
        cdb::ClauseDBIF,
        state::{State, StateIF},
        types::*,
    },
    std::{
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::Iter,
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
/// use crate::splr::processor::{Eliminator, EliminateIF};
/// use crate::splr::solver::Solver;

/// let mut s = Solver::instantiate(&Config::default(), &CNFDescription::default());
/// let elim = &mut s.elim;
/// assert_eq!(elim.is_running(), false);
/// elim.activate();
/// // At this point, the `elim` is in `ready` mode, not `running`.
/// assert_eq!(elim.is_running(), false);
/// assert_eq!(elim.simplify(&mut s.asg, &mut s.cdb, &mut s.state), Ok(()));
///```
pub trait EliminateIF: Export<(usize, usize, f64)> {
    /// set eliminator's mode to **ready**.
    fn activate(&mut self);
    /// set eliminator's mode to **dormant**.
    fn stop<A, C>(&mut self, asg: &mut A, cdb: &mut C)
    where
        A: AssignIF,
        C: ClauseDBIF;
    /// check if the eliminator is running.
    fn is_running(&self) -> bool;
    /// rebuild occur lists.
    fn prepare<A, C>(&mut self, asg: &mut A, cdb: &mut C, force: bool)
    where
        A: AssignIF,
        C: ClauseDBIF;
    /// enqueue a var into eliminator's var queue.
    fn enqueue_var<A>(&mut self, asg: &mut A, vi: VarId, upword: bool)
    where
        A: AssignIF;
    /// simplify database by:
    /// * removing satisfiable clauses
    /// * calling exhaustive simplifier that tries **clause subsumption** and **variable elimination**.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn simplify<A, C>(&mut self, asg: &mut A, cdb: &mut C, state: &mut State) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF;
    /// register a clause id to all corresponding occur lists.
    fn add_cid_occur<A>(&mut self, asg: &mut A, cid: ClauseId, c: &mut Clause, enqueue: bool)
    where
        A: AssignIF;
    /// remove a clause id from all corresponding occur lists.
    fn remove_cid_occur<A>(&mut self, asg: &mut A, cid: ClauseId, c: &mut Clause)
    where
        A: AssignIF;
    /// return the order of vars based on their occurrences
    fn sorted_iterator(&self) -> Iter<'_, usize>;
    /// return vi's stats
    fn stats(&self, vi: VarId) -> Option<(usize, usize)>;
    /// return eliminated literals.
    fn eliminated_lits(&self) -> &[Lit];
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

impl Export<(usize, usize, f64)> for Eliminator {
    /// exports:
    ///  1. the number of full eliminations
    ///  1. the number of satisfied clause eliminations
    ///
    ///```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use crate::splr::processor::Eliminator;
    /// let elim = Eliminator::instantiate(&Config::default(), &CNFDescription::default());
    /// let (elim_num_full_elimination, elim_num_sat_elimination, elim_to_simplify) = elim.exports();
    ///```
    #[inline]
    fn exports(&self) -> (usize, usize, f64) {
        (
            self.num_full_elimination,
            self.num_sat_elimination,
            self.to_simplify,
        )
    }
}

/// Mapping from Literal to Clauses.
#[derive(Debug)]
pub struct LitOccurs {
    aborted: bool,
    pos_occurs: Vec<ClauseId>,
    neg_occurs: Vec<ClauseId>,
}

impl Default for LitOccurs {
    fn default() -> LitOccurs {
        LitOccurs {
            aborted: false,
            pos_occurs: Vec::new(),
            neg_occurs: Vec::new(),
        }
    }
}

impl LitOccurs {
    /// return a new vector of $n$ `LitOccurs`s.
    pub fn new(n: usize) -> Vec<LitOccurs> {
        let mut vec = Vec::with_capacity(n + 1);
        for _ in 0..=n {
            vec.push(LitOccurs::default());
        }
        vec
    }
    pub fn clear(&mut self) {
        self.aborted = false;
        self.pos_occurs.clear();
        self.neg_occurs.clear();
    }
    pub fn activity(&self) -> usize {
        if self.aborted {
            std::usize::MAX
        } else {
            self.pos_occurs.len().min(self.neg_occurs.len())
        }
    }
}
/// Var heap structure based on the number of occurrences
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - `idxs[0]` contains the number of alive elements
///   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Debug)]
pub struct VarOccHeap {
    heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
}

/// Literal eliminator
#[derive(Debug)]
pub struct Eliminator {
    pub enable: bool,
    pub to_simplify: f64,
    mode: EliminatorMode,
    clause_queue: Vec<ClauseId>,
    var_queue: VarOccHeap,
    bwdsub_assigns: usize,
    elim_lits: Vec<Lit>,
    /// Maximum number of clauses to try to eliminate a var
    pub eliminate_var_occurrence_limit: usize,
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
            to_simplify: 0.0,
            mode: EliminatorMode::Deactive,
            var_queue: VarOccHeap::new(0, 0),
            clause_queue: Vec::new(),
            bwdsub_assigns: 0,
            elim_lits: Vec::new(),
            eliminate_var_occurrence_limit: 10_000,
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
            eliminate_var_occurrence_limit: config.elim_var_occ,
            eliminate_grow_limit: config.elim_grw_lim,
            subsume_literal_limit: config.elim_cls_lim,
            var: LitOccurs::new(nv + 1),
            ..Eliminator::default()
        }
    }
}

impl EliminateIF for Eliminator {
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
    fn stop<A, C>(&mut self, asg: &mut A, cdb: &mut C)
    where
        A: AssignIF,
        C: ClauseDBIF,
    {
        let force: bool = true;
        self.clear_clause_queue(cdb);
        self.clear_var_queue(asg);
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
    fn prepare<A, C>(&mut self, asg: &mut A, cdb: &mut C, force: bool)
    where
        A: AssignIF,
        C: ClauseDBIF,
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
            self.add_cid_occur(asg, ClauseId::from(cid), c, false);
        }
        if force {
            for vi in 1..=asg.var_stats().0 {
                if asg.var(vi).is(Flag::ELIMINATED) || asg.assign(vi).is_some() {
                    continue;
                }
                self.enqueue_var(asg, vi, true);
            }
        }
    }
    fn enqueue_var<A>(&mut self, asg: &mut A, vi: VarId, upward: bool)
    where
        A: AssignIF,
    {
        if self.mode != EliminatorMode::Running {
            return;
        }
        let w = &mut self[vi];
        if !asg.var(vi).is(Flag::ENQUEUED) && w.activity() < self.eliminate_occurrence_limit {
            asg.var_mut(vi).turn_on(Flag::ENQUEUED);
            self.var_queue.insert(&self.var, vi, upward);
        }
    }
    fn simplify<A, C>(&mut self, asg: &mut A, cdb: &mut C, state: &mut State) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF,
    {
        debug_assert_eq!(asg.decision_level(), 0);
        // we can reset all the reasons because decision level is zero.
        #[cfg(feature = "boundary_check")]
        {
            for v in asg.var_iter().skip(1) {
                if asg.reason(v.index) != AssignReason::None {
                    assert_eq!(asg.level(v.index), 0);
                    // asg.reason(v.index) = AssignReason::None;
                }
            }
        }
        if self.is_waiting() {
            self.prepare(asg, cdb, true);
        }
        self.eliminate(asg, cdb, state)?;
        self.num_sat_elimination += 1;
        if self.is_running() {
            self.num_full_elimination += 1;
            self.stop(asg, cdb);
        }
        cdb.check_size().map(|_| ())
    }
    fn add_cid_occur<A>(&mut self, asg: &mut A, cid: ClauseId, c: &mut Clause, enqueue: bool)
    where
        A: AssignIF,
    {
        if self.mode != EliminatorMode::Running || c.is(Flag::OCCUR_LINKED) {
            return;
        }
        let evo = self.eliminate_var_occurrence_limit;
        for l in &c.lits {
            let v = &mut asg.var_mut(l.vi());
            let w = &mut self[l.vi()];
            v.turn_on(Flag::TOUCHED);
            if evo < w.pos_occurs.len() + w.neg_occurs.len() {
                w.aborted = true;
                continue;
            }
            if !v.is(Flag::ELIMINATED) {
                if bool::from(*l) {
                    debug_assert!(
                        !w.pos_occurs.contains(&cid),
                        format!("{} {:?} {}", cid, c, v.index,)
                    );
                    w.pos_occurs.push(cid);
                } else {
                    debug_assert!(
                        !w.neg_occurs.contains(&cid),
                        format!("{} {:?} {}", cid, c, v.index,)
                    );
                    w.neg_occurs.push(cid);
                }
                self.enqueue_var(asg, l.vi(), false);
            }
        }
        c.turn_on(Flag::OCCUR_LINKED);
        if enqueue {
            self.enqueue_clause(cid, c);
        }
    }
    fn remove_cid_occur<A>(&mut self, asg: &mut A, cid: ClauseId, c: &mut Clause)
    where
        A: AssignIF,
    {
        debug_assert!(self.mode == EliminatorMode::Running);
        debug_assert!(!cid.is_lifted_lit());
        c.turn_off(Flag::OCCUR_LINKED);
        debug_assert!(c.is(Flag::DEAD));
        for l in &c.lits {
            if asg.assign(l.vi()).is_none() {
                self.remove_lit_occur(asg, *l, cid);
                self.enqueue_var(asg, l.vi(), true);
            }
        }
    }
    fn sorted_iterator(&self) -> Iter<'_, usize> {
        self.var_queue.heap[1..].iter()
    }
    fn stats(&self, vi: VarId) -> Option<(usize, usize)> {
        let w = &self[vi];
        if w.aborted {
            None
        } else {
            Some((w.pos_occurs.len(), w.neg_occurs.len()))
        }
    }
    fn eliminated_lits(&self) -> &[Lit] {
        &self.elim_lits
    }
}

impl Eliminator {
    /// check if the eliminator is active and waits for next `eliminate`.
    fn is_waiting(&self) -> bool {
        self.mode == EliminatorMode::Waiting
    }

    /// returns false if solver is inconsistent
    /// - calls `clause_queue.pop`
    fn backward_subsumption_check<A, C>(
        &mut self,
        asg: &mut A,
        cdb: &mut C,
        timedout: &Arc<AtomicBool>,
    ) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF,
    {
        debug_assert_eq!(asg.decision_level(), 0);
        while !self.clause_queue.is_empty() || self.bwdsub_assigns < asg.stack_len() {
            // Check top-level assignments by creating a dummy clause and placing it in the queue:
            if self.clause_queue.is_empty() && self.bwdsub_assigns < asg.stack_len() {
                let c = ClauseId::from(asg.stack(self.bwdsub_assigns));
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
                self.clear_var_queue(asg);
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
                    let v = &asg.var(l.vi());
                    let w = &self[l.vi()];
                    if asg.assign(l.vi()).is_some() || w.aborted {
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
            if best == 0 || asg.var(best).is(Flag::ELIMINATED) {
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
                            try_subsume(asg, cdb, self, cid, *did)?;
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
    fn eliminate<A, C>(&mut self, asg: &mut A, cdb: &mut C, state: &mut State) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF,
    {
        let start = state.elapsed().unwrap_or(0.0);
        loop {
            let na = asg.stack_len();
            self.eliminate_main(asg, cdb, state)?;
            cdb.eliminate_satisfied_clauses(asg, self, true);
            if na == asg.stack_len()
                && (!self.is_running()
                    || (0 == self.clause_queue_len() && 0 == self.var_queue_len()))
            {
                break;
            }
            if 0.1 <= state.elapsed().unwrap_or(1.0) - start {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(asg);
                break;
            }
        }
        Ok(())
    }
    /// do the elimination task
    fn eliminate_main<A, C>(
        &mut self,
        asg: &mut A,
        cdb: &mut C,
        state: &mut State,
    ) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF,
    {
        /// The ratio of time slot for single elimination step.
        /// Since it is measured in millisecond, 1000 means executing elimination
        /// until timed out. 100 means this function can consume 10% of a given time.
        const TIMESLOT_FOR_ELIMINATION: u64 = 10;
        debug_assert!(asg.decision_level() == 0);
        if self.mode == EliminatorMode::Deactive {
            return Ok(());
        }
        let timedout = Arc::new(AtomicBool::new(false));
        let timedout2 = timedout.clone();
        let time = if asg.exports().1 == 0 {
            100 * TIMESLOT_FOR_ELIMINATION * state.config.timeout as u64
        } else {
            TIMESLOT_FOR_ELIMINATION * state.config.timeout as u64
        };
        thread::spawn(move || {
            thread::sleep(Duration::from_millis(time));
            timedout2.store(true, Ordering::Release);
        });
        while self.bwdsub_assigns < asg.stack_len()
            || !self.var_queue.is_empty()
            || !self.clause_queue.is_empty()
        {
            if !self.clause_queue.is_empty() || self.bwdsub_assigns < asg.stack_len() {
                self.backward_subsumption_check(asg, cdb, &timedout)?;
            }
            while let Some(vi) = self.var_queue.select_var(&self.var, asg) {
                // timedout = cvar.wait(timedout).unwrap();
                let v = asg.var_mut(vi);
                v.turn_off(Flag::ENQUEUED);
                if !v.is(Flag::ELIMINATED) && asg.assign(vi).is_none() {
                    eliminate_var(asg, cdb, self, state, vi, &timedout)?;
                }
            }
            self.backward_subsumption_check(asg, cdb, &timedout)?;
            debug_assert!(self.clause_queue.is_empty());
            cdb.garbage_collect();
            if asg.propagate(cdb) != ClauseId::default() {
                return Err(SolverError::Inconsistent);
            }
            cdb.eliminate_satisfied_clauses(asg, self, true);
            if timedout.load(Ordering::Acquire) {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(asg);
            }
        }
        Ok(())
    }
    /// remove a clause id from literal's occur list.
    fn remove_lit_occur<A>(&mut self, asg: &mut A, l: Lit, cid: ClauseId)
    where
        A: AssignIF,
    {
        let w = &mut self[l.vi()];
        if w.aborted {
            return;
        }
        if bool::from(l) {
            debug_assert_eq!(w.pos_occurs.iter().filter(|&c| *c == cid).count(), 1);
            w.pos_occurs.delete_unstable(|&c| c == cid);
            debug_assert!(!w.pos_occurs.contains(&cid));
        } else {
            debug_assert_eq!(w.neg_occurs.iter().filter(|&c| *c == cid).count(), 1);
            w.neg_occurs.delete_unstable(|&c| c == cid);
            debug_assert!(!w.neg_occurs.contains(&cid));
        }
        self.enqueue_var(asg, l.vi(), true);
    }

    ///
    /// clause queue operations
    ///

    /// enqueue a clause into eliminator's clause queue.
    fn enqueue_clause(&mut self, cid: ClauseId, c: &mut Clause) {
        if self.mode != EliminatorMode::Running
            || c.is(Flag::ENQUEUED)
            || self.subsume_literal_limit < c.lits.len()
        {
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
    fn clear_var_queue<A>(&mut self, asg: &mut A)
    where
        A: AssignIF,
    {
        self.var_queue.clear(asg);
    }
    /// return the length of eliminator's var queue.
    fn var_queue_len(&self) -> usize {
        self.var_queue.len()
    }
}

#[allow(dead_code)]
fn check_eliminator<C>(cdb: &C, elim: &Eliminator) -> bool
where
    C: ClauseDBIF,
{
    // clause_queue should be clear.
    // all elements in occur_lists exist.
    // for v in asg {
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

#[cfg(test)]
mod tests {
    #![allow(unused_imports)]
    #![allow(unused_variables)]
    #![allow(dead_code)]
    use super::*;
    use crate::{cdb::ClauseDB, solver::Solver};

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

        let c1 = s
            .cdb
            .new_clause(&mut s.asg, &mut mkv![1, 2, 3], false, false);
        let c2 = s
            .cdb
            .new_clause(&mut s.asg, &mut mkv![-2, 3, 4], false, false);
        let c3 = s
            .cdb
            .new_clause(&mut s.asg, &mut mkv![-2, -3], false, false);
        let c4 = s
            .cdb
            .new_clause(&mut s.asg, &mut mkv![1, 2, -3, 9], false, false);
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

    // fn mk_c(s: &mut Solver, i: usize, v: Vec<i32>) -> ClauseId {
    //     let mut vec = v.iter().map(|i| Lit::from(*i)).collect::<Vec<Lit>>();
    //     let cid = s.cdb.new_clause(&mut vec, None::<&mut VarDB>);
    //     cid
    // }
}

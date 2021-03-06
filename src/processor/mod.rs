//!
//! * private module `eliminate` provides var elimination
//! * private module `subsume` provides clause subsumption
//!
//!# Example
//!
//!```
//!  use splr::{processor::{self, EliminateIF}, solver::Solver, types::PropertyDereference};
//!  use std::convert::TryFrom;
//!  let mut s = Solver::try_from("tests/sample.cnf").expect("failed to load");
//!  let Solver {
//!      ref mut asg,
//!      ref mut cdb,
//!      ref mut elim,
//!      ref mut state,
//!      ..
//!  } = s;
//!  elim.activate();
//!  elim.simplify(asg, cdb, state).expect("panic");
//!  assert_eq!(elim.derefer(processor::property::Tusize::NumFullElimination), 1);
//!  assert!(0 < asg.num_eliminated_vars);
//!```

mod eliminate;
mod heap;
mod subsume;

pub use self::property::*;

use {
    self::{eliminate::eliminate_var, heap::VarOrderIF},
    crate::{
        assign::{self, AssignIF},
        cdb::ClauseDBIF,
        solver::SolverEvent,
        state::{State, StateIF},
        types::*,
    },
    std::{
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::Iter,
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
pub trait EliminateIF {
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
    fn enqueue_var<A>(&mut self, asg: &mut A, vi: VarId, upward: bool)
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
    /// return the constraints on eliminated literals.
    fn eliminated_lits(&self) -> &[Lit];
}

/// API for getting stats about Eliminator's internal data.
pub trait EliminatorStatIF {
    fn stats(&self) -> (usize, usize);
}

#[derive(Copy, Clone, Eq, Debug, PartialEq)]
enum EliminatorMode {
    Dormant,
    Waiting,
    Running,
}

/// Mapping from Literal to Clauses.
#[derive(Clone, Debug)]
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
    pub fn is_empty(&self) -> bool {
        self.pos_occurs.is_empty() && self.neg_occurs.is_empty()
    }
    pub fn len(&self) -> usize {
        self.pos_occurs.len() + self.neg_occurs.len()
    }
}
/// Var heap structure based on the number of occurrences
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - `idxs[0]` contains the number of alive elements
///   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Clone, Debug)]
pub struct VarOccHeap {
    heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
}

/// Literal eliminator
#[derive(Clone, Debug)]
pub struct Eliminator {
    pub enable: bool,
    pub to_simplify: f64,
    mode: EliminatorMode,
    clause_queue: Vec<ClauseId>,
    var_queue: VarOccHeap,
    bwdsub_assigns: usize,
    /// constraints on eliminated var. It is used by `extend_model`.
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
    num_subsumed: usize,
}

impl Default for Eliminator {
    fn default() -> Eliminator {
        Eliminator {
            #[cfg(not(feature = "clause_elimination"))]
            enable: false,
            #[cfg(feature = "clause_elimination")]
            enable: true,
            to_simplify: 0.0,
            mode: EliminatorMode::Dormant,
            var_queue: VarOccHeap::new(0, 0),
            clause_queue: Vec::new(),
            bwdsub_assigns: 0,
            elim_lits: Vec::new(),
            eliminate_var_occurrence_limit: 1_000,
            eliminate_combination_limit: 80,
            eliminate_grow_limit: 0, // 64
            eliminate_occurrence_limit: 800,
            subsume_literal_limit: 100,
            var: Vec::new(),
            num_full_elimination: 0,
            num_sat_elimination: 0,
            num_subsumed: 0,
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
            var_queue: VarOccHeap::new(nv, 0),
            eliminate_var_occurrence_limit: config.elm_var_occ,
            eliminate_grow_limit: config.elm_grw_lim,
            subsume_literal_limit: config.elm_cls_lim,
            var: LitOccurs::new(nv + 1),
            ..Eliminator::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        match e {
            SolverEvent::NewVar => {
                let len = self.var_queue.heap.len();
                self.var.push(LitOccurs::default());
                self.var_queue.heap.push(len);
                self.var_queue.idxs.push(len);
                self.var_queue.idxs[0] = len;
            }
            SolverEvent::Reinitialize => {
                self.elim_lits.clear();
            }
            _ => (),
        }
    }
}

pub mod property {
    use super::Eliminator;
    use crate::types::*;

    #[derive(Clone, Debug, PartialEq)]
    pub enum Tusize {
        NumClauseSubsumption,
        NumFullElimination,
        NumSatElimination,
    }

    impl PropertyDereference<Tusize, usize> for Eliminator {
        #[inline]
        fn derefer(&self, k: Tusize) -> usize {
            match k {
                Tusize::NumClauseSubsumption => self.num_subsumed,
                Tusize::NumFullElimination => self.num_full_elimination,
                Tusize::NumSatElimination => self.num_sat_elimination,
            }
        }
    }
}

impl EliminateIF for Eliminator {
    fn activate(&mut self) {
        if self.enable {
            debug_assert!(self.mode != EliminatorMode::Running);
            self.mode = EliminatorMode::Waiting;
        }
    }
    fn is_running(&self) -> bool {
        self.enable && self.mode == EliminatorMode::Running
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
        self.mode = EliminatorMode::Dormant;
    }
    fn prepare<A, C>(&mut self, asg: &mut A, cdb: &mut C, force: bool)
    where
        A: AssignIF,
        C: ClauseDBIF,
    {
        debug_assert!(self.enable);
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
            for vi in 1..=asg.derefer(assign::property::Tusize::NumVar) {
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
        if self.enable {
            if self.is_waiting() {
                self.prepare(asg, cdb, true);
            }
            self.eliminate(asg, cdb, state)?;
            if self.is_running() {
                self.stop(asg, cdb);
            }
        } else {
            self.eliminate_satisfied_clauses(asg, cdb, true);
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
            let pl = w.pos_occurs.len();
            let nl = w.neg_occurs.len();
            if evo < pl * nl {
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
        timedout: &mut usize,
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
            if *timedout == 0 {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(asg);
                return Ok(());
            }
            let best = if cid.is_lifted_lit() {
                Lit::from(cid).vi()
            } else {
                let mut tmp = cdb.count();
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
                        let d = &cdb[*did];
                        if d.len() <= *timedout {
                            *timedout -= d.len();
                        } else {
                            *timedout = 0;
                            return Ok(());
                        }
                        if !d.is(Flag::DEAD) && d.len() <= self.subsume_literal_limit {
                            self.try_subsume(asg, cdb, cid, *did)?;
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
            self.eliminate_satisfied_clauses(asg, cdb, true);
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
        self.num_full_elimination += 1;
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
        debug_assert!(asg.decision_level() == 0);
        if self.mode == EliminatorMode::Dormant {
            return Ok(());
        }
        let mut timedout: usize = {
            let nv = asg.num_unasserted() as f64;
            let nc = cdb.count() as f64;
            (6.0 * nv.log2() * nc) as usize
        };
        while self.bwdsub_assigns < asg.stack_len()
            || !self.var_queue.is_empty()
            || !self.clause_queue.is_empty()
        {
            if !self.clause_queue.is_empty() || self.bwdsub_assigns < asg.stack_len() {
                self.backward_subsumption_check(asg, cdb, &mut timedout)?;
            }
            while let Some(vi) = self.var_queue.select_var(&self.var, asg) {
                let v = asg.var_mut(vi);
                v.turn_off(Flag::ENQUEUED);
                if !v.is(Flag::ELIMINATED) && asg.assign(vi).is_none() {
                    eliminate_var(asg, cdb, self, state, vi, &mut timedout)?;
                }
            }
            self.backward_subsumption_check(asg, cdb, &mut timedout)?;
            debug_assert!(self.clause_queue.is_empty());
            cdb.garbage_collect();
            if !asg.propagate(cdb).is_none() {
                return Err(SolverError::Inconsistent);
            }
            self.eliminate_satisfied_clauses(asg, cdb, true);
            if timedout == 0 {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(asg);
            } else {
                timedout -= 1;
            }
        }
        Ok(())
    }
    /// delete satisfied clauses at decision level zero.
    pub fn eliminate_satisfied_clauses<A, C>(
        &mut self,
        asg: &mut A,
        cdb: &mut C,
        update_occur: bool,
    ) where
        A: AssignIF,
        C: ClauseDBIF,
    {
        debug_assert_eq!(asg.decision_level(), 0);
        self.num_sat_elimination += 1;
        for ci in 1..cdb.len() {
            let cid = ClauseId::from(ci);
            if !cdb[cid].is(Flag::DEAD) && asg.satisfies(&cdb[cid].lits) {
                cdb.detach(cid);
                let c = &mut cdb[cid];
                if self.is_running() {
                    if update_occur {
                        self.remove_cid_occur(asg, cid, c);
                    }
                    for l in &c.lits {
                        self.enqueue_var(asg, l.vi(), true);
                    }
                }
            }
        }
        cdb.garbage_collect();
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

#[cfg(not(feature = "no_IO"))]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assign::VarManipulateIF, processor::EliminateIF, solver::Solver};
    use std::convert::TryFrom;

    #[test]
    fn check_elimination() {
        let mut config = Config::default();
        config.quiet_mode = true;
        let mut s = Solver::try_from("tests/sample.cnf").expect("failed to load");
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut elim,
            ref mut state,
            ..
        } = s;
        assert!(elim.enable);
        // elim.eliminate_combination_limit = 2;
        // elim.eliminate_occurrence_limit = 1;
        // elim.subsume_literal_limit = 1;
        elim.activate();
        elim.simplify(asg, cdb, state).expect("");
        assert_eq!(elim.num_full_elimination, 1);
        assert!(!asg.var_iter().skip(1).all(|v| v.is(Flag::ELIMINATED)));
        assert!(0 < asg.num_eliminated_vars);
        assert_eq!(
            asg.num_eliminated_vars,
            asg.var_iter().filter(|v| v.is(Flag::ELIMINATED)).count()
        );
        let elim_vars = asg
            .var_iter()
            .filter(|v| v.is(Flag::ELIMINATED))
            .map(|v| v.index)
            .collect::<Vec<_>>();
        assert_eq!(
            0,
            cdb.iter()
                .skip(1)
                .filter(|c| !c.is(Flag::DEAD))
                .filter(|c| c.lits.iter().any(|l| elim_vars.contains(&l.vi())))
                .count()
        );
    }
}

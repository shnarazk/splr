/// Crate `propagator` implements Boolean Constraint Propagation and decision var selection.
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    crate::{
        clause::{ClauseDBIF, WatchDBIF},
        state::State,
        types::*,
        var::{VarDBIF, VarRewardIF},
    },
    std::{
        fmt,
        fs::File,
        io::{BufWriter, Write},
        ops::{Index, Range, RangeFrom},
        slice::Iter,
    },
};

/// API for assignment like `propagate`, `enqueue`, `cancel_until`, and so on.
pub trait PropagatorIF: Index<usize, Output = Lit> {
    /// return the number of assignments.
    fn len(&self) -> usize;
    /// return the number of assignments at a given decision level `u`.
    ///
    /// ## Caveat
    /// - it emits a panic by out of index range.
    /// - it emits a panic if the level is 0.
    fn len_upto(&self, n: DecisionLevel) -> usize;
    /// return `true` if there's no assignment.
    fn is_empty(&self) -> bool;
    /// return an iterator over assignment stack.
    fn iter(&self) -> Iter<'_, Lit>;
    /// return the current decision level.
    fn level(&self) -> DecisionLevel;
    ///return the decision var's id at that level.
    fn decision_vi(&self, lv: DecisionLevel) -> VarId;
    /// return `true` if the current decision level is zero.
    fn is_zero(&self) -> bool;
    /// return `true` if there are unpropagated assignments.
    fn remains(&self) -> bool;
    /// add an assignment at level 0 as a precondition.
    ///
    /// # Errors
    ///
    /// emit `SolverError::Inconsistent` exception if solver becomes inconsistent.
    fn assign_at_rootlevel<V>(&mut self, vdb: &mut V, l: Lit) -> MaybeInconsistent
    where
        V: VarDBIF + VarRewardIF;
    /// unsafe enqueue (assign by implication); doesn't emit an exception.
    ///
    /// ## Warning
    /// Caller must assure the consistency after this assignment
    fn assign_by_implication<V>(
        &mut self,
        vdb: &mut V,
        l: Lit,
        reason: AssignReason,
        lv: DecisionLevel,
    ) where
        V: VarDBIF + VarRewardIF;
    /// unsafe assume (assign by decision); doesn't emit an exception.
    /// ## Caveat
    /// Callers have to assure the consistency after this assignment.
    fn assign_by_decision<V>(&mut self, vdb: &mut V, l: Lit)
    where
        V: VarDBIF + VarRewardIF;
    /// fix a var's assignment by a unit learnt clause.
    /// ## Caveat
    /// - Callers have to assure the consistency after this assignment.
    /// - No need to restart; but execute `propagate` just afterward.
    fn assign_by_unitclause<V>(&mut self, vdb: &mut V, l: Lit)
    where
        V: VarDBIF + VarRewardIF;
    /// execute *backjump*.
    fn cancel_until<V>(&mut self, vdb: &mut V, lv: DecisionLevel)
    where
        V: VarDBIF + VarRewardIF;
    /// execute *boolean constraint propagation* or *unit propagation*.
    fn propagate<C, V>(&mut self, cdb: &mut C, vdb: &mut V) -> ClauseId
    where
        C: ClauseDBIF,
        V: VarDBIF + VarRewardIF;
    /// return `true` if subsequential propagations emit the same conflict.
    fn recurrent_conflicts(&self) -> bool;
}

/// API for var selection.
pub trait VarSelectionIF {
    /// select a new decision variable.
    fn select_var<V>(&mut self, vdb: &mut V) -> VarId
    where
        V: VarDBIF + VarRewardIF;
    /// update the internal heap on var order.
    fn update_order<V>(&mut self, vdb: &mut V, v: VarId)
    where
        V: VarDBIF + VarRewardIF;
    /// rebuild the internal var_order
    fn rebuild_order<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF + VarRewardIF;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssignReason {
    /// One of not assigned, assigned by decision, or solved.
    None,
    /// Assigned by a clause. If it is binary, the reason literal is stored in the 2nd.
    Implication(ClauseId, Lit),
}

impl Default for AssignReason {
    fn default() -> AssignReason {
        AssignReason::None
    }
}

impl fmt::Display for AssignReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AssignReason::None => write!(f, "reason:none"),
            AssignReason::Implication(c, NULL_LIT) => write!(f, "reason:{}", c),
            AssignReason::Implication(c, _) => write!(f, "reason:biclause{}", c),
        }
    }
}

/// A record of assignment. It's called 'trail' in Glucose.
#[derive(Debug)]
pub struct AssignStack {
    pub trail: Vec<Lit>,
    asgvec: Vec<Option<bool>>,
    trail_lim: Vec<usize>,
    q_head: usize,
    root_level: DecisionLevel,
    conflicts: (VarId, VarId),
    var_order: VarIdHeap, // Variable Order

    //
    //## Statistics
    //
    num_conflict: usize,
    num_propagation: usize,
    num_restart: usize,
}

impl Default for AssignStack {
    fn default() -> AssignStack {
        AssignStack {
            trail: Vec::new(),
            asgvec: Vec::new(),
            trail_lim: Vec::new(),
            q_head: 0,
            root_level: 0,
            conflicts: (0, 0),
            var_order: VarIdHeap::default(),
            num_conflict: 0,
            num_propagation: 0,
            num_restart: 0,
        }
    }
}

/// ```
/// let x: Lbool = var_assign!(self, lit.vi());
/// ```
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.asgvec.get_unchecked($var) }
    };
}

macro_rules! lit_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l => {
                #[allow(unused_unsafe)]
                // unsafe { *$asg.asgvec.get_unchecked(l.vi()) ^ (l as u8 & 1) }
                match unsafe { *$asg.asgvec.get_unchecked(l.vi()) } {
                    Some(x) if !bool::from(l) => Some(!x),
                    x => x,
                }
            }
        }
    };
}

macro_rules! set_assign {
    ($asg: expr, $lit: expr) => {
        match $lit {
            l => unsafe {
                *$asg.asgvec.get_unchecked_mut(l.vi()) = Some(bool::from(l));
            },
        }
    };
}

#[allow(unused_unsafe)]
macro_rules! unset_assign {
    ($asg: expr, $var: expr) => {
        unsafe {
            *$asg.asgvec.get_unchecked_mut($var) = None;
        }
    };
}

impl Index<usize> for AssignStack {
    type Output = Lit;
    #[inline]
    fn index(&self, i: usize) -> &Lit {
        unsafe { self.trail.get_unchecked(i) }
    }
}

impl Index<Range<usize>> for AssignStack {
    type Output = [Lit];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Lit] {
        &self.trail[r]
    }
}

impl Index<RangeFrom<usize>> for AssignStack {
    type Output = [Lit];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Lit] {
        unsafe { self.trail.get_unchecked(r) }
    }
}

impl<'a> IntoIterator for &'a mut AssignStack {
    type Item = &'a Lit;
    type IntoIter = Iter<'a, Lit>;
    fn into_iter(self) -> Self::IntoIter {
        self.trail.iter()
    }
}

impl From<&mut AssignStack> for Vec<i32> {
    fn from(asgs: &mut AssignStack) -> Vec<i32> {
        asgs.trail.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
    }
}

impl Instantiate for AssignStack {
    fn instantiate(_cfg: &Config, cnf: &CNFDescription) -> AssignStack {
        let nv = cnf.num_of_variables;
        AssignStack {
            asgvec: vec![None; 1 + nv],
            trail: Vec::with_capacity(nv),
            var_order: VarIdHeap::new(nv, nv),
            ..AssignStack::default()
        }
    }
}

impl Export<(usize, usize, usize)> for AssignStack {
    /// exports:
    ///  1. the number of conflicts
    ///  1. the number of propagations
    ///  1. the number of restarts
    ///
    ///```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use crate::splr::propagator::AssignStack;
    /// let asgs = AssignStack::instantiate(&Config::default(), &CNFDescription::default());
    /// let (asgs_num_conflict, asgs_num_propagation, asgs_num_restart) = asgs.exports();
    ///```
    #[inline]
    fn exports(&self) -> (usize, usize, usize) {
        (self.num_conflict, self.num_propagation, self.num_restart)
    }
}

impl PropagatorIF for AssignStack {
    fn len(&self) -> usize {
        self.trail.len()
    }
    fn len_upto(&self, n: DecisionLevel) -> usize {
        self.trail_lim[n as usize]
    }
    fn is_empty(&self) -> bool {
        self.trail.is_empty()
    }
    fn iter(&self) -> Iter<'_, Lit> {
        self.trail.iter()
    }
    fn level(&self) -> DecisionLevel {
        self.trail_lim.len() as DecisionLevel
    }
    fn decision_vi(&self, lv: DecisionLevel) -> VarId {
        debug_assert!(0 < lv);
        self.trail[self.trail_lim[lv as usize - 1]].vi()
    }
    fn is_zero(&self) -> bool {
        self.trail_lim.is_empty()
    }
    fn remains(&self) -> bool {
        self.q_head < self.trail.len()
    }
    fn assign_at_rootlevel<V>(&mut self, vdb: &mut V, l: Lit) -> MaybeInconsistent
    where
        V: VarDBIF + VarRewardIF,
    {
        let vi = l.vi();
        debug_assert!(vi < vdb.len());
        vdb.level_mut()[vi] = 0;
        let v = &mut vdb[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        debug_assert_eq!(0, self.level());
        match var_assign!(self, v.index) {
            None => {
                set_assign!(self, l);
                v.assign = Some(bool::from(l));
                v.reason = AssignReason::None;
                debug_assert!(!self.trail.contains(&!l));
                self.trail.push(l);
                Ok(())
            }
            Some(x) if x == bool::from(l) => Ok(()),
            _ => Err(SolverError::Inconsistent),
        }
    }
    fn assign_by_implication<V>(
        &mut self,
        vdb: &mut V,
        l: Lit,
        reason: AssignReason,
        lv: DecisionLevel,
    ) where
        V: VarDBIF + VarRewardIF,
    {
        debug_assert!(usize::from(l) != 0, "Null literal is about to be equeued");
        debug_assert!(l.vi() < vdb.len());
        // The following doesn't hold anymore by using chronoBT.
        // assert!(self.trail_lim.is_empty() || cid != ClauseId::default());
        let vi = l.vi();
        vdb.level_mut()[vi] = lv;
        let v = &mut vdb[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        debug_assert!(
            var_assign!(self, vi) == Some(bool::from(l)) || var_assign!(self, vi).is_none()
        );
        set_assign!(self, l);
        v.assign = Some(bool::from(l));
        v.reason = reason;
        vdb.reward_at_assign(vi);
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
    }
    fn assign_by_decision<V>(&mut self, vdb: &mut V, l: Lit)
    where
        V: VarDBIF + VarRewardIF,
    {
        debug_assert!(l.vi() < vdb.len());
        debug_assert!(!self.trail.contains(&l));
        debug_assert!(!self.trail.contains(&!l), format!("{:?}", l));
        self.level_up();
        let dl = self.trail_lim.len() as DecisionLevel;
        let vi = l.vi();
        vdb.level_mut()[vi] = dl;
        let v = &mut vdb[vi];
        debug_assert!(!v.is(Flag::ELIMINATED));
        // debug_assert!(self.assign[vi] == l.lbool() || self.assign[vi] == BOTTOM);
        set_assign!(self, l);
        v.assign = Some(bool::from(l));
        v.reason = AssignReason::default();
        vdb.reward_at_assign(vi);
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
    }
    fn assign_by_unitclause<V>(&mut self, vdb: &mut V, l: Lit)
    where
        V: VarDBIF + VarRewardIF,
    {
        self.cancel_until(vdb, self.root_level);
        debug_assert!(self.trail.iter().all(|k| k.vi() != l.vi()));
        let vi = l.vi();
        vdb.level_mut()[vi] = 0;
        let v = &mut vdb[l];
        set_assign!(self, l);
        v.assign = Some(bool::from(l));
        v.reason = AssignReason::default();
        vdb.clear_reward(l.vi());
        debug_assert!(!self.trail.contains(&!l));
        self.trail.push(l);
    }
    fn cancel_until<V>(&mut self, vdb: &mut V, lv: DecisionLevel)
    where
        V: VarDBIF + VarRewardIF,
    {
        if self.trail_lim.len() as u32 <= lv {
            return;
        }
        let lim = self.trail_lim[lv as usize];
        let mut shift = lim;
        for i in lim..self.trail.len() {
            let l = self.trail[i];
            let vi = l.vi();
            if vdb.level_mut()[vi] <= lv {
                self.trail[shift] = l;
                shift += 1;
                continue;
            }
            let v = &mut vdb[vi];
            unset_assign!(self, vi);
            v.set(Flag::PHASE, v.assign.unwrap());
            v.assign = None;
            v.reason = AssignReason::default();
            vdb.reward_at_unassign(vi);
            self.var_order.insert(vdb, vi);
        }
        self.trail.truncate(shift);
        debug_assert!(self.trail.iter().all(|l| vdb[*l].assign.is_some()));
        debug_assert!(self.trail.iter().all(|k| !self.trail.contains(&!*k)));
        self.trail_lim.truncate(lv as usize);
        // assert!(lim < self.q_head) dosen't hold sometimes in chronoBT.
        self.q_head = self.q_head.min(lim);
        if lv == self.root_level {
            self.num_restart += 1;
        }
    }
    /// UNIT PROPAGATION.
    /// Note:
    ///  - *Precondition*: no checking dead clauses. They cause crash.
    ///  - This function assumes there's no dead clause.
    ///    So Eliminator should call `garbage_collect` before me.
    ///  - The order of literals in binary clauses will be modified to hold
    ///    propagatation order.
    fn propagate<C, V>(&mut self, cdb: &mut C, vdb: &mut V) -> ClauseId
    where
        C: ClauseDBIF,
        V: VarDBIF + VarRewardIF,
    {
        let watcher = cdb.watcher_lists_mut() as *mut [Vec<Watch>];
        let check_index = self.num_conflict + self.num_restart;
        unsafe {
            let level = vdb.level_mut() as *const [DecisionLevel];
            self.num_propagation += 1;
            while let Some(p) = self.trail.get(self.q_head) {
                self.q_head += 1;
                let false_lit = !*p;
                let source = (*watcher).get_unchecked_mut(usize::from(*p));
                let mut n = 0;
                'next_clause: while n < source.len() {
                    let w = source.get_unchecked_mut(n);
                    n += 1;
                    let blocker_value = lit_assign!(self, w.blocker);
                    if blocker_value == Some(true) {
                        continue 'next_clause;
                    }
                    if w.binary {
                        if blocker_value == Some(false) {
                            self.conflicts.1 = self.conflicts.0;
                            self.conflicts.0 = false_lit.vi();
                            self.num_conflict += 1;
                            return w.c;
                        }
                        self.assign_by_implication(
                            vdb,
                            w.blocker,
                            AssignReason::Implication(w.c, false_lit),
                            (*level)[false_lit.vi()],
                        );
                        continue 'next_clause;
                    }
                    // debug_assert!(!cdb[w.c].is(Flag::DEAD));
                    let Clause {
                        ref mut lits,
                        ref mut checked_at,
                        ref mut search_from,
                        ..
                    } = cdb[w.c];
                    debug_assert!(lits[0] == false_lit || lits[1] == false_lit);
                    let mut first = *lits.get_unchecked(0);
                    if first == false_lit {
                        first = *lits.get_unchecked(1);
                        lits.swap(0, 1);
                    }
                    let first_value = lit_assign!(self, first);
                    if first != w.blocker && first_value == Some(true) {
                        w.blocker = first;
                        continue 'next_clause;
                    }
                    //
                    //## Skip checked falsified literals
                    //
                    if *checked_at < check_index {
                        *checked_at = check_index;
                        *search_from = 2;
                    }
                    for (k, lk) in lits.iter().enumerate().skip(*search_from) {
                        if lit_assign!(self, *lk) != Some(false) {
                            (*watcher)
                                .get_unchecked_mut(usize::from(!*lk))
                                .register(first, w.c, false);
                            n -= 1;
                            source.detach(n);
                            lits.swap(1, k);
                            *search_from = k + 1;
                            continue 'next_clause;
                        }
                    }
                    if first_value == Some(false) {
                        self.conflicts.1 = self.conflicts.0;
                        self.conflicts.0 = false_lit.vi();
                        self.num_conflict += 1;
                        return w.c;
                    }
                    let lv = lits[1..]
                        .iter()
                        .map(|l| (*level)[l.vi()])
                        .max()
                        .unwrap_or(0);
                    self.assign_by_implication(
                        vdb,
                        first,
                        AssignReason::Implication(w.c, NULL_LIT),
                        lv,
                    );
                }
            }
        }
        ClauseId::default()
    }
    fn recurrent_conflicts(&self) -> bool {
        self.conflicts.0 == self.conflicts.1
    }
}

impl VarSelectionIF for AssignStack {
    fn select_var<V>(&mut self, vdb: &mut V) -> VarId
    where
        V: VarDBIF + VarRewardIF,
    {
        self.var_order.select_var(vdb)
    }
    fn update_order<V>(&mut self, vdb: &mut V, v: VarId)
    where
        V: VarDBIF + VarRewardIF,
    {
        self.var_order.update(vdb, v)
    }
    fn rebuild_order<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF + VarRewardIF,
    {
        self.var_order.rebuild(vdb);
    }
}

impl AssignStack {
    fn level_up(&mut self) {
        self.trail_lim.push(self.trail.len());
    }
    /// dump all active clauses and fixed assignments as a CNF file.
    #[allow(dead_code)]
    fn dump_cnf<C, V>(&mut self, cdb: &C, state: &State, vdb: &V, fname: &str)
    where
        C: ClauseDBIF,
        V: VarDBIF,
    {
        for v in vdb.iter().skip(1) {
            if v.is(Flag::ELIMINATED) {
                if var_assign!(self, v.index).is_some() {
                    panic!(
                        "conflicting var {} {:?}",
                        v.index,
                        var_assign!(self, v.index)
                    );
                } else {
                    println!("eliminate var {}", v.index);
                }
            }
        }
        if let Ok(out) = File::create(&fname) {
            let mut buf = BufWriter::new(out);
            let nv = self.len();
            let nc: usize = cdb.len() - 1;
            buf.write_all(format!("p cnf {} {}\n", state.num_vars, nc + nv).as_bytes())
                .unwrap();
            for c in cdb.iter().skip(1) {
                for l in &c.lits {
                    buf.write_all(format!("{} ", i32::from(*l)).as_bytes())
                        .unwrap();
                }
                buf.write_all(b"0\n").unwrap();
            }
            buf.write_all(b"c from trail\n").unwrap();
            for x in &self.trail {
                buf.write_all(format!("{} 0\n", i32::from(*x)).as_bytes())
                    .unwrap();
            }
        }
    }
}

/// Heap of VarId, based on var activity.
// # Note
// - both fields has a fixed length. Don't use push and pop.
// - `idxs[0]` contains the number of alive elements
//   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Debug)]
pub struct VarIdHeap {
    heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
}

impl Default for VarIdHeap {
    fn default() -> VarIdHeap {
        VarIdHeap {
            heap: Vec::new(),
            idxs: Vec::new(),
        }
    }
}

trait VarOrderIF {
    fn new(n: usize, init: usize) -> VarIdHeap;
    fn update<V>(&mut self, vdb: &mut V, v: VarId)
    where
        V: VarRewardIF;
    fn insert<V>(&mut self, vdb: &mut V, vi: VarId)
    where
        V: VarRewardIF;
    fn clear(&mut self);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn select_var<V>(&mut self, vdb: &mut V) -> VarId
    where
        V: VarDBIF + VarRewardIF;
    fn rebuild<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF + VarRewardIF;
}

impl VarOrderIF for VarIdHeap {
    fn new(n: usize, init: usize) -> VarIdHeap {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(n);
        for i in 1..=n {
            heap.push(i);
            idxs.push(i);
        }
        idxs[0] = init;
        VarIdHeap { heap, idxs }
    }
    fn update<V>(&mut self, vdb: &mut V, v: VarId)
    where
        V: VarRewardIF,
    {
        debug_assert!(v != 0, "Invalid VarId");
        let start = self.idxs[v];
        if self.contains(v) {
            self.percolate_up(vdb, start)
        }
    }
    fn insert<V>(&mut self, vdb: &mut V, vi: VarId)
    where
        V: VarRewardIF,
    {
        if self.contains(vi) {
            let i = self.idxs[vi];
            self.percolate_up(vdb, i);
            return;
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n];
        self.heap.swap(i, n);
        self.idxs.swap(vi, vn);
        self.idxs[0] = n;
        self.percolate_up(vdb, n);
    }
    fn clear(&mut self) {
        self.reset()
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
    fn select_var<V>(&mut self, vdb: &mut V) -> VarId
    where
        V: VarDBIF + VarRewardIF,
    {
        loop {
            let vi = self.get_root(vdb);
            if vdb[vi].assign.is_none() && !vdb[vi].is(Flag::ELIMINATED) {
                return vi;
            }
        }
    }
    fn rebuild<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF + VarRewardIF,
    {
        self.reset();
        for vi in 1..vdb.len() {
            if vdb[vi].assign.is_none() && !vdb[vi].is(Flag::ELIMINATED) {
                self.insert(vdb, vi);
            }
        }
    }
}

impl fmt::Display for AssignStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let v = self.trail.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
        let len = self.level();
        let c = |i| {
            let a = self.len_upto(i);
            match i {
                0 => (0, &v[0..a]),
                x if x == len - 1 => (i + 1, &v[a..]),
                x => (x + 1, &v[a..self.len_upto(x + 1)]),
            }
        };
        if 0 < len {
            write!(f, "{:?}", (0..len).map(c).collect::<Vec<_>>())
        } else {
            write!(f, "# - trail[  0]  [0{:?}]", &v)
        }
    }
}

impl VarIdHeap {
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn reset(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    fn get_root<V>(&mut self, vdb: &mut V) -> VarId
    where
        V: VarRewardIF,
    {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        let vn = self.heap[n];
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(vdb, 1);
        }
        vs
    }
    fn percolate_up<V>(&mut self, vdb: &mut V, start: usize)
    where
        V: VarRewardIF,
    {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = vdb.activity(vq);
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vdb.activity(vp);
                if ap < aq {
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
    fn percolate_down<V>(&mut self, vdb: &mut V, start: usize)
    where
        V: VarRewardIF,
    {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i];
        let ai = vdb.activity(vi);
        loop {
            let l = 2 * i; // left
            if l < n {
                let vl = self.heap[l];
                let al = vdb.activity(vl);
                let r = l + 1; // right
                let (target, vc, ac) = if r < n && al < vdb.activity(self.heap[r]) {
                    let vr = self.heap[r];
                    (r, vr, vdb.activity(vr))
                } else {
                    (l, vl, al)
                };
                if ai < ac {
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
    fn remove<V>(&mut self, vdb: &mut V, vs: VarId)
    where
        V: VarRewardIF,
    {
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
            self.percolate_down(vdb, 1);
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

impl fmt::Display for VarIdHeap {
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
    use super::*;
    use crate::var::VarDB;

    fn lit(i: i32) -> Lit {
        Lit::from(i)
    }
    #[test]
    fn test_propagation() {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut vardb = VarDB::instantiate(&config, &cnf);
        let vdb = &mut vardb;
        let mut asgs = AssignStack::instantiate(&config, &cnf);
        // [] + 1 => [1]
        assert!(asgs.assign_at_rootlevel(vdb, lit(1)).is_ok());
        assert_eq!(asgs.trail, vec![lit(1)]);

        // [1] + 1 => [1]
        assert!(asgs.assign_at_rootlevel(vdb, lit(1)).is_ok());
        assert_eq!(asgs.trail, vec![lit(1)]);

        // [1] + 2 => [1, 2]
        assert!(asgs.assign_at_rootlevel(vdb, lit(2)).is_ok());
        assert_eq!(asgs.trail, vec![lit(1), lit(2)]);

        // [1, 2] + -1 => ABORT & [1, 2]
        assert!(asgs.assign_at_rootlevel(vdb, lit(-1)).is_err());
        assert_eq!(asgs.level(), 0);
        assert_eq!(asgs.len(), 2);

        // [1, 2] + 3 => [1, 2, 3]
        asgs.assign_by_decision(vdb, lit(3));
        assert_eq!(asgs.trail, vec![lit(1), lit(2), lit(3)]);
        assert_eq!(asgs.level(), 1);
        assert_eq!(asgs.len(), 3);
        assert_eq!(asgs.len_upto(0), 2);

        // [1, 2, 3] + 4 => [1, 2, 3, 4]
        asgs.assign_by_decision(vdb, lit(4));
        assert_eq!(asgs.trail, vec![lit(1), lit(2), lit(3), lit(4)]);
        assert_eq!(asgs.level(), 2);
        assert_eq!(asgs.len(), 4);
        assert_eq!(asgs.len_upto(1), 3);

        // [1, 2, 3] => [1, 2]
        asgs.cancel_until(vdb, 1);
        assert_eq!(asgs.trail, vec![lit(1), lit(2), lit(3)]);
        assert_eq!(asgs.level(), 1);
        assert_eq!(asgs.len(), 3);
        assert_eq!(asgs.trail_lim, vec![2]);
        assert_eq!(vdb.assigned(lit(1)), Some(true));
        assert_eq!(vdb.assigned(lit(-1)), Some(false));
        assert_eq!(vdb.assigned(lit(4)), None);

        // [1, 2, 3] => [1, 2, 3, 4]
        asgs.assign_by_decision(vdb, lit(4));
        assert_eq!(asgs.trail, vec![lit(1), lit(2), lit(3), lit(4)]);
        assert_eq!(vdb[lit(4)].level, 2);
        assert_eq!(asgs.trail_lim, vec![2, 3]);

        // [1, 2, 3, 4] => [1, 2, -4]
        asgs.assign_by_unitclause(vdb, Lit::from(-4i32));
        assert_eq!(asgs.trail, vec![lit(1), lit(2), lit(-4)]);
        assert_eq!(asgs.level(), 0);
        assert_eq!(asgs.len(), 3);

        assert_eq!(vdb.assigned(lit(-4)), Some(true));
        assert_eq!(vdb.assigned(lit(-3)), None);
    }
}

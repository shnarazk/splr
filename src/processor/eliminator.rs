use {
    super::{
        eliminate::eliminate_var,
        heap::{LitOccurs, VarOccHeap, VarOrderIF},
        EliminateIF, Eliminator, EliminatorMode,
    },
    crate::{
        assign::{self, AssignIF},
        cdb::{self, ClauseDBIF},
        solver::{restart::RestartIF, SolverEvent},
        state::{State, StateIF},
        types::*,
    },
    std::{
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::Iter,
    },
};

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
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(i)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.var[i]
    }
}

impl IndexMut<VarId> for Eliminator {
    #[inline]
    fn index_mut(&mut self, i: VarId) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked_mut(i)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.var[i]
    }
}

impl Index<&VarId> for Eliminator {
    type Output = LitOccurs;
    #[inline]
    fn index(&self, i: &VarId) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(*i)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.var[*i]
    }
}

impl IndexMut<&VarId> for Eliminator {
    #[inline]
    fn index_mut(&mut self, i: &VarId) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked_mut(*i)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.var[*i]
    }
}

impl Index<Lit> for Eliminator {
    type Output = LitOccurs;
    #[inline]
    fn index(&self, l: Lit) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(l.vi())
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.var[l.vi()]
    }
}

impl IndexMut<Lit> for Eliminator {
    #[inline]
    fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked_mut(l.vi())
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.var[l.vi()]
    }
}

impl Index<&Lit> for Eliminator {
    type Output = LitOccurs;
    #[inline]
    fn index(&self, l: &Lit) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(l.vi())
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.var[l.vi()]
    }
}

impl IndexMut<&Lit> for Eliminator {
    #[inline]
    fn index_mut(&mut self, l: &Lit) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked_mut(l.vi())
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.var[l.vi()]
    }
}

impl Index<Range<usize>> for Eliminator {
    type Output = [LitOccurs];
    #[inline]
    fn index(&self, r: Range<usize>) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.var[r]
    }
}

impl Index<RangeFrom<usize>> for Eliminator {
    type Output = [LitOccurs];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.var[r]
    }
}

impl IndexMut<Range<usize>> for Eliminator {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked_mut(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.var[r]
    }
}

impl IndexMut<RangeFrom<usize>> for Eliminator {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.var.get_unchecked_mut(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
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
            if c.is_dead() || c.is(Flag::OCCUR_LINKED) {
                continue;
            }
            let vec = c.iter().copied().collect::<Vec<_>>();
            assert!(vec.iter().all(|l| !vec.contains(&!*l)));
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
    fn simplify<A, C, R>(
        &mut self,
        asg: &mut A,
        cdb: &mut C,
        rst: &mut R,
        state: &mut State,
    ) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF,
        R: RestartIF,
    {
        self.to_simplify = 0.0;
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
            self.subsume_literal_limit = (state.config.elm_cls_lim
                + cdb.derefer(cdb::property::Tf64::DpAverageLBD) as usize)
                / 2;
            if self.is_waiting() {
                self.prepare(asg, cdb, true);
            }
            self.eliminate(asg, cdb, rst, state)?;
            if self.is_running() {
                self.stop(asg, cdb);
            }
        } else {
            // self.eliminate_satisfied_clauses(asg, cdb, true);
            if let Some(cc) = asg.propagate(cdb).to_option() {
                return Err(SolverError::RootLevelConflict(cc));
            }
        }
        if self.mode != EliminatorMode::Dormant {
            self.stop(asg, cdb);
        }
        cdb.check_size().map(|_| ())
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
    /// register a clause id to all corresponding occur lists.
    pub fn add_cid_occur<A>(&mut self, asg: &mut A, cid: ClauseId, c: &mut Clause, enqueue: bool)
    where
        A: AssignIF,
    {
        if self.mode != EliminatorMode::Running || c.is(Flag::OCCUR_LINKED) {
            return;
        }
        let evo = self.eliminate_var_occurrence_limit;
        let mut checked: Vec<VarId> = Vec::new();
        for l in c.iter() {
            let vi = l.vi();
            let v = &mut asg.var_mut(vi);
            assert!(!checked.contains(&vi), "elimitator350: {:?}", c,);
            checked.push(vi);
            let w = &mut self[l.vi()];
            let pl = w.pos_occurs.len();
            let nl = w.neg_occurs.len();
            if evo < pl * nl {
                w.aborted = true;
                continue;
            }
            if !v.is(Flag::ELIMINATED) {
                if bool::from(*l) {
                    assert!(
                        !w.pos_occurs.contains(&cid),
                        "elim.add_cid_occur for {:?} found a strange positive clause{}{}, {:?}",
                        v,
                        cid,
                        c,
                        w.pos_occurs,
                    );
                    w.pos_occurs.push(cid);
                } else {
                    assert!(
                        !w.neg_occurs.contains(&cid),
                        "elim.add_cid_occur for {:?} found a strange negative clause{}{}, {:?}",
                        v,
                        cid,
                        c,
                        w.pos_occurs,
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
    /// remove a clause id from all corresponding occur lists.
    pub fn remove_cid_occur<A>(&mut self, asg: &mut A, cid: ClauseId, c: &mut Clause)
    where
        A: AssignIF,
    {
        debug_assert!(self.mode == EliminatorMode::Running);
        debug_assert!(!cid.is_lifted_lit());
        assert!(!c.is_dead());
        c.turn_off(Flag::OCCUR_LINKED);
        for l in c.iter() {
            if asg.assign(l.vi()).is_none() {
                self.remove_lit_occur(asg, *l, cid);
                self.enqueue_var(asg, l.vi(), true);
            }
        }
    }
    /// check if the eliminator is active and waits for next `eliminate`.
    fn is_waiting(&self) -> bool {
        self.mode == EliminatorMode::Waiting
    }
    /// set eliminator's mode to **dormant**.
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
    /// returns false if solver is inconsistent
    /// - calls `clause_queue.pop`
    pub fn backward_subsumption_check<A, C>(
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
            let best: VarId = if cid.is_lifted_lit() {
                let vi = Lit::from(cid).vi();
                debug_assert!(!asg.var(vi).is(Flag::ELIMINATED));
                vi
            } else {
                let mut tmp = cdb.derefer(cdb::property::Tusize::NumClause);
                let c = &mut cdb[cid];
                c.turn_off(Flag::ENQUEUED);
                if c.is_dead() || self.subsume_literal_limit < c.len() {
                    continue;
                }
                // if c is subsumed by c', both of c and c' are included in the occurs of all literals of c
                // so searching the shortest occurs is most efficient.
                let mut b = 0;
                for l in c.iter() {
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
            self[best].pos_occurs.retain(|cid| !cdb[*cid].is_dead());
            self[best].neg_occurs.retain(|cid| !cdb[*cid].is_dead());
            for cls in [self[best].pos_occurs.clone(), self[best].neg_occurs.clone()].iter() {
                for did in cls.iter() {
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
                    if !d.is_dead() && d.len() <= self.subsume_literal_limit {
                        assert!(
                            d.contains(Lit::from((best, false)))
                                || d.contains(Lit::from((best, true)))
                        );
                        self.try_subsume(asg, cdb, cid, *did)?;
                    }
                }
            }
            self[best].pos_occurs.retain(|cid| !cdb[*cid].is_dead());
            self[best].neg_occurs.retain(|cid| !cdb[*cid].is_dead());
        }
        if asg.remains() {
            if let Some(cc) = asg.propagate(cdb).to_option() {
                return Err(SolverError::RootLevelConflict(cc));
            }
        }
        Ok(())
    }
    /// run clause subsumption and variable elimination.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn eliminate<A, C, R>(
        &mut self,
        asg: &mut A,
        cdb: &mut C,
        rst: &mut R,
        state: &mut State,
    ) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF,
        R: RestartIF,
    {
        let start = state.elapsed().unwrap_or(0.0);
        loop {
            let na = asg.stack_len();
            self.eliminate_main(asg, cdb, rst, state)?;
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
    fn eliminate_main<A, C, R>(
        &mut self,
        asg: &mut A,
        cdb: &mut C,
        rst: &mut R,
        state: &mut State,
    ) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF,
        R: RestartIF,
    {
        debug_assert!(asg.decision_level() == 0);
        if self.mode == EliminatorMode::Dormant {
            return Ok(());
        }
        let mut timedout: usize = {
            let nv = asg.derefer(assign::property::Tusize::NumUnassertedVar) as f64;
            let nc = cdb.derefer(cdb::property::Tusize::NumClause) as f64;
            (6.0 * nv.log(1.5) * nc) as usize
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
                    eliminate_var(asg, cdb, self, rst, state, vi, &mut timedout)?;
                }
            }
            self.backward_subsumption_check(asg, cdb, &mut timedout)?;
            debug_assert!(self.clause_queue.is_empty());
            if let Some(cc) = asg.propagate(cdb).to_option() {
                return Err(SolverError::RootLevelConflict(cc));
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
            if !cdb[cid].is_dead() && cdb[cid].is_satisfied_under(asg) {
                if self.is_running() {
                    let c = &mut cdb[cid];
                    if update_occur {
                        self.remove_cid_occur(asg, cid, c);
                    }
                    for l in c.iter() {
                        self.enqueue_var(asg, l.vi(), true);
                    }
                }
                // cdb.watches(cid, "eliminator645");
                cdb.remove_clause(cid);
            }
        }
    }
    /// remove a clause id from literal's occur list.
    pub fn remove_lit_occur<A>(&mut self, asg: &mut A, l: Lit, cid: ClauseId)
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
    pub fn enqueue_clause(&mut self, cid: ClauseId, c: &mut Clause) {
        if self.mode != EliminatorMode::Running
            || c.is(Flag::ENQUEUED)
            || self.subsume_literal_limit < c.len()
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
        if c.is_dead() {
            continue;
        }
        for l in c.iter() {
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

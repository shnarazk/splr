use {
    super::{
        eliminate::eliminate_var,
        heap::{LitOccurs, VarOccHeap, VarOrderIF},
        EliminateIF, Eliminator, EliminatorMode,
    },
    crate::{
        assign::{self, AssignIF},
        cdb::{self, ClauseDBIF},
        state::{self, State, StateIF},
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
            enable: cfg!(feature = "clause_elimination"),
            mode: EliminatorMode::Dormant,
            var_queue: VarOccHeap::new(0, 0),
            clause_queue: Vec::new(),
            bwdsub_assigns: 0,
            elim_lits: Vec::new(),
            eliminate_var_occurrence_limit: 1_000,
            eliminate_grow_limit: 0, // 64
            eliminate_occurrence_limit: 800,
            subsume_literal_limit: 100,
            var: Vec::new(),
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
            enable: config.enable_eliminator,
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
                self.var_queue.heap.push(len as u32);
                self.var_queue.idxs.push(len as u32);
                self.var_queue.idxs[0] = len as u32;
            }
            SolverEvent::Reinitialize => {
                self.elim_lits.clear();
            }
            _ => (),
        }
    }
}

impl EliminateIF for Eliminator {
    fn is_running(&self) -> bool {
        self.enable && self.mode == EliminatorMode::Running
    }
    fn prepare(&mut self, asg: &mut impl AssignIF, cdb: &mut impl ClauseDBIF, force: bool) {
        if !self.enable {
            return;
        }
        // debug_assert!(self.enable);
        debug_assert_eq!(self.mode, EliminatorMode::Dormant);
        self.mode = EliminatorMode::Running;
        for w in &mut self[1..] {
            w.clear();
        }
        for (cid, c) in &mut cdb.iter_mut().enumerate().skip(1) {
            if c.is_dead() || c.is(FlagClause::OCCUR_LINKED) {
                continue;
            }
            let vec = c.iter().copied().collect::<Vec<_>>();
            debug_assert!(vec.iter().all(|l| !vec.contains(&!*l)));
            self.add_cid_occur(asg, ClauseId::from(cid), c, false);
        }
        if force {
            for vi in 1..=asg.derefer(assign::property::Tusize::NumVar) {
                if asg.var(vi).is(FlagVar::ELIMINATED) || asg.assign(vi).is_some() {
                    continue;
                }
                self.enqueue_var(asg, vi, true);
            }
        }
        debug_assert_eq!(self.mode, EliminatorMode::Running);
    }
    fn enqueue_var(&mut self, asg: &mut impl AssignIF, vi: VarId, upward: bool) {
        if self.mode != EliminatorMode::Running {
            return;
        }
        let w = &mut self[vi];
        if !asg.var(vi).is(FlagVar::ENQUEUED) && w.activity() < self.eliminate_occurrence_limit {
            asg.var_mut(vi).turn_on(FlagVar::ENQUEUED);
            self.var_queue.insert(&self.var, vi, upward);
        }
    }
    fn simplify(
        &mut self,
        asg: &mut impl AssignIF,
        cdb: &mut impl ClauseDBIF,
        state: &mut State,
        force_run: bool,
    ) -> MaybeInconsistent {
        debug_assert_eq!(asg.decision_level(), 0);
        // we can reset all the reasons because decision level is zero.
        #[cfg(feature = "boundary_check")]
        {
            for (i, _) in asg.var_iter().enumerate().skip(1) {
                if asg.reason(i) != AssignReason::None {
                    assert_eq!(
                        asg.level(i),
                        asg.derefer(assign::property::Tusize::RootLevel) as DecisionLevel
                    );
                    // asg.reason(v.index) = AssignReason::None;
                }
            }
        }
        if self.enable {
            if !force_run && self.mode == EliminatorMode::Dormant {
                self.prepare(asg, cdb, true);
            }
            self.eliminate_grow_limit = state.derefer(state::property::Tusize::IntervalScale) / 2;
            self.subsume_literal_limit = state.config.elm_cls_lim
                + cdb.derefer(cdb::property::Tf64::LiteralBlockEntanglement) as usize;
            debug_assert!(!cdb
                .derefer(cdb::property::Tf64::LiteralBlockEntanglement)
                .is_nan());
            // self.eliminate_combination_limit = cdb.derefer(cdb::property::Tf64::LiteralBlockEntanglement);
            self.eliminate(asg, cdb, state)?;
        } else {
            asg.propagate_sandbox(cdb)
                .map_err(SolverError::RootLevelConflict)?;
        }
        if self.mode != EliminatorMode::Dormant {
            self.stop(asg, cdb);
        }
        for occur in self.var.iter_mut() {
            occur.clear();
        }
        self.var_queue.clear(asg);
        debug_assert!(self.clause_queue.is_empty());
        cdb.check_size().map(|_| ())
    }
    fn sorted_iterator(&self) -> Iter<'_, u32> {
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
    fn eliminated_lits(&mut self) -> &mut Vec<Lit> {
        &mut self.elim_lits
    }
}

impl Eliminator {
    /// register a clause id to all corresponding occur lists.
    pub fn add_cid_occur(
        &mut self,
        asg: &mut impl AssignIF,
        cid: ClauseId,
        c: &mut Clause,
        enqueue: bool,
    ) {
        if self.mode != EliminatorMode::Running || c.is(FlagClause::OCCUR_LINKED) {
            return;
        }
        let evo = self.eliminate_var_occurrence_limit;
        let mut checked: Vec<VarId> = Vec::new();
        for l in c.iter() {
            let vi = l.vi();
            let v = &mut asg.var_mut(vi);
            debug_assert!(
                !checked.contains(&vi),
                "eliminator::add_cid_occur356: {c:?}"
            );
            checked.push(vi);
            let w = &mut self[l.vi()];
            let pl = w.pos_occurs.len();
            let nl = w.neg_occurs.len();
            if evo < pl * nl {
                w.aborted = true;
                continue;
            }
            if !v.is(FlagVar::ELIMINATED) {
                if bool::from(*l) {
                    debug_assert!(
                        !w.pos_occurs.contains(&cid),
                        "elim.add_cid_occur for {:?} found a strange positive clause{}{}, {:?}",
                        v,
                        cid,
                        c,
                        w.pos_occurs,
                    );
                    w.pos_occurs.push(cid);
                } else {
                    debug_assert!(
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
        c.turn_on(FlagClause::OCCUR_LINKED);
        if enqueue {
            self.enqueue_clause(cid, c);
        }
    }
    /// remove a clause id from all corresponding occur lists.
    pub fn remove_cid_occur(&mut self, asg: &mut impl AssignIF, cid: ClauseId, c: &mut Clause) {
        debug_assert!(self.mode == EliminatorMode::Running);
        debug_assert!(!cid.is_lifted_lit());
        debug_assert!(!c.is_dead());
        c.turn_off(FlagClause::OCCUR_LINKED);
        for l in c.iter() {
            if asg.assign(l.vi()).is_none() {
                self.remove_lit_occur(asg, *l, cid);
                self.enqueue_var(asg, l.vi(), true);
            }
        }
    }
    /// set eliminator's mode to **dormant**.
    // Due to a potential bug of killing clauses and difficulty about
    // synchronization between 'garbage_collect' and clearing occur lists,
    // 'stop' should purge all occur lists to purge any dead clauses for now.
    fn stop(&mut self, asg: &mut impl AssignIF, cdb: &mut impl ClauseDBIF) {
        let force: bool = true;
        self.clear_clause_queue(cdb);
        self.clear_var_queue(asg);
        if force {
            for c in &mut cdb.iter_mut().skip(1) {
                c.turn_off(FlagClause::OCCUR_LINKED);
            }
            for w in &mut self[1..] {
                w.clear();
            }
        }
        self.mode = EliminatorMode::Dormant;
    }
    /// returns false if solver is inconsistent
    /// - calls `clause_queue.pop`
    pub fn backward_subsumption_check(
        &mut self,
        asg: &mut impl AssignIF,
        cdb: &mut impl ClauseDBIF,
        timedout: &mut usize,
    ) -> MaybeInconsistent {
        debug_assert_eq!(asg.decision_level(), 0);
        while !self.clause_queue.is_empty() || self.bwdsub_assigns < asg.stack_len() {
            // Check top-level assignments by creating a dummy clause
            // and placing it in the queue:
            if self.clause_queue.is_empty() && self.bwdsub_assigns < asg.stack_len() {
                let c = ClauseId::from(asg.stack(self.bwdsub_assigns));
                self.clause_queue.push(c);
                self.bwdsub_assigns += 1;
            }
            if let Some(cid) = self.clause_queue.pop() {
                if *timedout == 0 {
                    self.clear_clause_queue(cdb);
                    self.clear_var_queue(asg);
                    return Ok(());
                }
                let best: VarId = if cid.is_lifted_lit() {
                    let vi = Lit::from(cid).vi();
                    debug_assert!(!asg.var(vi).is(FlagVar::ELIMINATED));
                    vi
                } else {
                    let mut tmp = cdb.derefer(cdb::property::Tusize::NumClause);
                    let c = &mut cdb[cid];
                    c.turn_off(FlagClause::ENQUEUED);
                    if c.is_dead() || self.subsume_literal_limit < c.len() {
                        continue;
                    }
                    // if c is subsumed by c', both of c and c' are included in
                    // the occurs of all literals of c
                    // so searching the shortest occurs is most efficient.
                    let mut b = 0;
                    for l in c.iter() {
                        let v = &asg.var(l.vi());
                        let w = &self[l.vi()];
                        if asg.assign(l.vi()).is_some() || w.aborted {
                            continue;
                        }
                        let num_sum = if bool::from(*l) {
                            w.neg_occurs.len()
                        } else {
                            w.pos_occurs.len()
                        };
                        if !v.is(FlagVar::ELIMINATED) && num_sum < tmp {
                            b = l.vi();
                            tmp = num_sum;
                        }
                    }
                    b
                };
                if best == 0 || asg.var(best).is(FlagVar::ELIMINATED) {
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
                            debug_assert!(
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
        }
        if asg.remains() {
            asg.propagate_sandbox(cdb)
                .map_err(SolverError::RootLevelConflict)?;
        }
        Ok(())
    }
    /// run clause subsumption and variable elimination.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn eliminate(
        &mut self,
        asg: &mut impl AssignIF,
        cdb: &mut impl ClauseDBIF,
        state: &mut State,
    ) -> MaybeInconsistent {
        let start = state.elapsed().unwrap_or(0.0);
        loop {
            let na = asg.stack_len();
            self.eliminate_main(asg, cdb, state)?;
            asg.propagate_sandbox(cdb)
                .map_err(SolverError::RootLevelConflict)?;
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
    fn eliminate_main(
        &mut self,
        asg: &mut impl AssignIF,
        cdb: &mut impl ClauseDBIF,
        state: &mut State,
    ) -> MaybeInconsistent {
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
                v.turn_off(FlagVar::ENQUEUED);
                if !v.is(FlagVar::ELIMINATED) && asg.assign(vi).is_none() {
                    eliminate_var(asg, cdb, self, state, vi, &mut timedout)?;
                }
            }
            self.backward_subsumption_check(asg, cdb, &mut timedout)?;
            debug_assert!(self.clause_queue.is_empty());
            asg.propagate_sandbox(cdb)
                .map_err(SolverError::RootLevelConflict)?;
            if timedout == 0 {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(asg);
            } else {
                timedout -= 1;
            }
        }
        Ok(())
    }
    /// remove a clause id from literal's occur list.
    pub fn remove_lit_occur(&mut self, asg: &mut impl AssignIF, l: Lit, cid: ClauseId) {
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

    //
    // clause queue operations
    //

    /// enqueue a clause into eliminator's clause queue.
    pub fn enqueue_clause(&mut self, cid: ClauseId, c: &mut Clause) {
        if self.mode != EliminatorMode::Running
            || c.is(FlagClause::ENQUEUED)
            || self.subsume_literal_limit < c.len()
        {
            return;
        }
        self.clause_queue.push(cid);
        c.turn_on(FlagClause::ENQUEUED);
    }
    /// clear eliminator's clause queue.
    fn clear_clause_queue(&mut self, cdb: &mut impl ClauseDBIF) {
        for cid in &self.clause_queue {
            cdb[*cid].turn_off(FlagClause::ENQUEUED);
        }
        self.clause_queue.clear();
    }
    /// return the length of eliminator's clause queue.
    fn clause_queue_len(&self) -> usize {
        self.clause_queue.len()
    }

    //
    // var queue operations
    //

    /// clear eliminator's var queue
    fn clear_var_queue(&mut self, asg: &mut impl AssignIF) {
        self.var_queue.clear(asg);
    }
    /// return the length of eliminator's var queue.
    fn var_queue_len(&self) -> usize {
        self.var_queue.len()
    }
}

#[allow(dead_code)]
fn check_eliminator(cdb: &impl ClauseDBIF, elim: &Eliminator) -> bool {
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

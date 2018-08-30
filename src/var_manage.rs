#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_imports)]
use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause::ClausePack;
use clause::CLAUSE_KINDS;
use clause_manage::KINDS;
use clause_manage::ClauseManagement;
use solver::SatSolver;
use solver::SolverException::*;
use solver::SolverResult;
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use solver_rollback::Restart;
use std::usize::MAX;
use types::*;
use var::AccessHeap;
use var::Satisfiability;
use var::Var;
use var::VarIdHeap;
use var::VarOrder;
use var::VarOrdering;

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;
const SUBSUMPTION_LIMIT: usize = 1_000_000;

pub trait VarSelect {
    fn select_var(&mut self) -> VarId;
    fn bump_vi(&mut self, vi: VarId) -> ();
    fn decay_var_activity(&mut self) -> ();
    fn rebuild_vh(&mut self) -> ();
}

impl VarSelect for Solver {
    fn rebuild_vh(&mut self) -> () {
        if self.decision_level() != 0 {
            return;
        }
        self.var_order.reset();
        for vi in 1..self.vars.len() {
            if self.vars[vi].assign == BOTTOM {
                self.var_order.insert(&self.vars, vi);
            }
        }
    }
    fn bump_vi(&mut self, vi: VarId) -> () {
        let d = self.stats[Stat::NumOfBackjump as usize] as f64;
        let a = (self.vars[vi].activity + d) / 2.0;
        self.vars[vi].activity = a;
        if VAR_ACTIVITY_THRESHOLD < a {
            // self.rescale_var_activity();
            for i in 1..self.vars.len() {
                self.vars[i].activity = self.vars[i].activity / VAR_ACTIVITY_THRESHOLD;
            }
            self.var_inc /= VAR_ACTIVITY_THRESHOLD;
        }
        self.var_order.update(&self.vars, vi);
    }
    fn decay_var_activity(&mut self) -> () {
        self.var_inc = self.var_inc / VAR_ACTIVITY_THRESHOLD;
    }
    /// Heap operations; renamed from selectVO
    fn select_var(&mut self) -> VarId {
        loop {
            if self.var_order.len() == 0 {
                return 0;
            }
            let vi = self.var_order.root(&self.vars);
            let x = self.vars[vi].assign;
            if x == BOTTOM {
                return vi;
            }
        }
    }
}

impl Solver {
    /// 4. removeClause
    /// called from strengthen_clause, backward_subsumption_check, eliminate_var, substitute
    pub fn remove_clause(&mut self, cid: ClauseId) -> () {
        let Solver {
            ref mut cp,
            ref mut vars,
            ref mut eliminator,
            ..
        } = self;
        let mut c = &mut cp[cid.to_kind()].clauses[cid.to_index()];
        for i in 0..c.lits.len() + 2 {
            let vi = lindex!(c, i).vi();
            vars[vi].num_occur -= 1;
            // eliminator.update_heap(vars, vi);
        }
        // solver::removeClause(...)
        c.index = MAX;
    }
    /// 5. strengthenClause
    pub fn strengthen_clause(&mut self, cid: ClauseId, l: Lit) -> bool {
        let rank;
        let c0;
        let empty;
        {
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            debug_assert_ne!(cid, NULL_CLAUSE);
            self.eliminator.subsumption_queue.push(cid);
            if c.lits.is_empty() {
                empty = true; // substitute 'self.remove_clause(cid);'
                c.strengthen(l);
            } else {
                // detachClause(cid);
                c.strengthen(l);
                // attachClause(cid);
                // remove(occurs[var(l)], cid);
                // self.vars[l.vi()].occurs.retain(|&ci| ci != cid);
                if 1 < self.vars[l.vi()].num_occur {
                    self.vars[l.vi()].num_occur -= 1;
                }
                // self.eliminator.update_heap(&self.vars, l.vi());
                empty = false;
            }
            // println!("strengthen_clause done {}", c);
            rank = c.rank;
            c0 = c.lit[0];
        }
        if empty {
            self.remove_clause(cid);
        }
        if rank == 0 {
            // rank = 0 is for unit clause
            self.enqueue(c0, NULL_CLAUSE) && self.propagate() == NULL_CLAUSE
        } else {
            true
        }
    }
    /// 6. merge(1)
    /// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
    pub fn merge(&mut self, cp: ClauseId, cq: ClauseId, v: VarId) -> bool {
        self.eliminator.merges += 1;
        self.eliminator.merge_vec.clear();
        let pq = &self.cp[cp.to_kind()].clauses[cp.to_index()];
        let qp = &self.cp[cq.to_kind()].clauses[cq.to_index()];
        let ps_smallest = pq.len() < qp.len();
        let (p, q) = if ps_smallest { (pq, qp) } else { (qp, pq) };
        'next_literal: for i in 0..q.len() {
            let l = lindex!(q, i);
            if l.vi() != v {
                for j in 0..p.len() {
                    let m = lindex!(p, j);
                    if m.vi() == l.vi() {
                        if m.negate() == l {
                            return false;
                        } else {
                            continue 'next_literal;
                        }
                    }
                }
                self.eliminator.merge_vec.push(l);
            }
        }
        for i in 0..p.len() {
            let l = lindex!(p, i);
            if l.vi() != v {
                self.eliminator.merge_vec.push(l);
            }
        }
        true
    }
    /// 7. merge(2)
    /// Returns **false** if one of the clauses is always satisfied.
    pub fn merge_(&mut self, cp: ClauseId, cq: ClauseId, v: VarId) -> (bool, usize) {
        self.eliminator.merges += 1;
        let pq = &self.cp[cp.to_kind()].clauses[cp.to_index()];
        let qp = &self.cp[cq.to_kind()].clauses[cq.to_index()];
        let ps_smallest = pq.len() < qp.len();
        let (p, q) = if ps_smallest { (pq, qp) } else { (qp, pq) };
        let mut size = p.len() - 1;
        'next_literal: for i in 0..q.len() {
            let l = lindex!(q, i);
            if l.vi() != v {
                for j in 0..p.len() {
                    let m = lindex!(p, j);
                    if m.vi() == l.vi() {
                        if m.negate() == l {
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
    /// 8. gatherTouchedClauses
    pub fn gather_touched_clauses(&mut self) -> () {
        self.eliminator.subsumption_queue.clear();
        self.eliminator.targets.clear();
        for kind in &[ClauseKind::Binclause, ClauseKind::Removable, ClauseKind::Permanent] {
            let clauses = &self.cp[*kind as usize].clauses;
            let exhaustive = clauses.len() < SUBSUMPTION_LIMIT;
            'next_clause: for i in 1..clauses.len() {
                let c = &clauses[i];
                for j in 1..c.len() {
                    let l = lindex!(c, j);
                    if exhaustive || l.vi() == self.eliminator.best_v {
                        self.eliminator.subsumption_queue.push(kind.id_from(i));
                        self.eliminator.targets.push(kind.id_from(i));
                        continue 'next_clause;
                    }
                }
            }
        }
    }
    /// 10. backwardSubsumptionCheck
    pub fn backward_subsumption_check(&mut self) -> bool {
        // println!("backward_subsumption_check {}", self.eliminator.subsumption_queue.len());
        let mut cnt = 0;
        let mut subsumed = 0;
        let mut deleted_literals = 0;
        debug_assert_eq!(self.decision_level(), 0);
        while 0 < self.eliminator.subsumption_queue.len()
            || self.eliminator.bwdsub_assigns < self.trail.len()
        {
            // Empty subsumption queue and return immediately on user-interrupt:
            // if computed-too-long { break; }
            // Check top-level assigments by creating a dummy clause and placing it in the queue:
            if self.eliminator.subsumption_queue.len() == 0
                && self.eliminator.bwdsub_assigns < self.trail.len()
            {
                let l: Lit = self.trail[self.eliminator.bwdsub_assigns];
                self.eliminator.bwdsub_assigns += 1;
                self.eliminator.bwdsub_tmp_clause.lit[0] = l;
                // self.eliminator.bwdsub_tmp_unit.calcAbstraction();
                self.eliminator
                    .subsumption_queue
                    .push(self.eliminator.bwdsub_tmp_clause_id);
            }
            let cid = self.eliminator.subsumption_queue[0];
            self.eliminator.subsumption_queue.remove(0);
            unsafe {
                let c = if cid == self.eliminator.bwdsub_tmp_clause_id {
                    &self.eliminator.bwdsub_tmp_clause as *const Clause
                } else {
                    &self.cp[cid.to_kind()].clauses[cid.to_index()] as *const Clause
                };
                if (*c).sve_mark {
                    continue;
                }
                // println!("check with {} for best_v {}", *c, self.eliminator.best_v);
                debug_assert!(1 < (*c).len() || self.assigned((*c).lit[0]) == LTRUE);
                // unit clauses should have been propagated before this point.
                // Find best variable to scan:
                //                'next_clause: for c in &self.cp[ClauseKind::Removable as usize].clauses {
                //                    let mut flag = false;
                //                    for i in 0 .. c.len() {
                //                        let l = lindex!(c, i);
                //                        if l.vi() == best_v {
                //                            // self.eliminator.subsumption_queue.push(ClauseKind::Removable.id_from(c.index));
                //                            debug_assert_eq!(c.index, i);
                //                            self.eliminator.targets.push(ClauseKind::Removable.id_from(i));
                //                            continue 'next_clause;
                //                        }
                //                    }
                //                }

                // Search all candidates:
                let cs = &self.eliminator.targets as *const Vec<ClauseId>;
                for ci in &*cs {
                    // let d = &self.cp[ci.to_kind()].clauses[ci.to_index()] as *const Clause;
                    let d = &self.cp[ci.to_kind()].clauses[ci.to_index()] as *const Clause;
                    if (*c).sve_mark {
                        continue;
                    }
                    if !(*d).sve_mark && *ci != cid && self.eliminator.subsumption_lim == 0
                        || (*d).len() < self.eliminator.subsumption_lim
                    {
                        // println!("{} + {}", *c, *d);
                        match (*c).subsumes(&*d) {
                            Some(NULL_LIT) => {
                                println!("    => subsumed completely");
                                subsumed += 1;
                                self.remove_clause(*ci);
                            }
                            Some(l) => {
                                // println!("     => subsumed {} by {}", *d, l.int());
                                deleted_literals += 1;
                                if !self.strengthen_clause(*ci, l.negate()) {
                                    return false;
                                }
                                // if l.vi() == best_v {
                                //     j -= 1;
                                // }
                            }
                            None => { }
                        }
                    }
                }
                self.eliminator.targets.clear();
            }
        }
        true
    }
    /// 13. mkElimClause(1)
    pub fn make_eliminating_clause(&self, vec: &mut Vec<Lit>, x: Lit) -> () {
        vec.push(x);
        vec.push(1);
    }
    /// 14. mkElimClause(2)
    pub fn make_eliminating_clause_(&self, vec: &mut Vec<Lit>, vi: VarId, cid: ClauseId) -> () {
        let first = vec.len();
        // Copy clause to the vector. Remember the position where the varibale 'v' occurs:
        let c = iref!(self.cp, cid);
        for i in 0..c.len() {
            let l = lindex!(c, i);
            vec.push(l as u32);
            if l.vi() == vi {
                let index = vec.len() - 1;
                // swap the first literal with the 'v'. So that the literal containing 'v' will occur first in the clause.
                vec.swap(index, first);
            }
        }
        // FIXME WHY? Store the length of the clause last:
        vec.push(c.len() as u32);
    }
    /// 15. eliminateVar
    pub fn eliminate_var(&mut self, v: VarId) -> bool {
        let mut cls = Vec::new();
        for ck in &KINDS {
            for c in &mut self.cp[*ck as usize].clauses {
                for i in 0..c.len() {
                    let l = lindex!(c, i);
                    if l.vi() == v {
                        cls.push(ck.id_from(i));
                    }
                }
            }
        }
        unsafe {
            // let cls = &self.vars[v].occurs as *const Vec<ClauseId>;
            let mut pos: Vec<ClauseId> = Vec::new();
            let mut neg: Vec<ClauseId> = Vec::new();
            // Split the occurrences into positive and negative:
            for cid in &*cls {
                let c = &self.cp[cid.to_kind()].clauses[cid.to_index()];
                if c.index == MAX {
                    continue;
                }
                for i in 0..c.len() {
                    let l = lindex!(c, i);
                    if l.vi() == v {
                        if l.positive() {
                            pos.push(*cid);
                        } else {
                            neg.push(*cid);
                        }
                    }
                }
            }
            // Check wether the increase in number of clauses stays within the allowed ('grow').
            // Moreover, no clause must exceed the limit on the maximal clause size (if it is set).
            let mut cnt = 0;
            for i in 0..pos.len() {
                for j in 0..neg.len() {
                    let (res, clause_size) = self.merge_(pos[i], neg[j], v);
                    if res {
                        cnt += 1;
                        if (*cls).len() < cnt
                            || (self.eliminator.clause_lim != 0
                                && self.eliminator.clause_lim < clause_size)
                        {
                            return true;
                        }
                    }
                }
            }
            // Delete and store old clauses
            self.vars[v].eliminated = true;
            println!("var {} was eliminated!", v);
            // setDecisionVar(v, false);
            self.eliminator.eliminated_vars += 1;
            {
                let tmp = &mut self.eliminator.elim_clauses as *mut Vec<Lit>;
                if neg.len() < pos.len() {
                    for cid in &neg {
                        self.make_eliminating_clause_(&mut (*tmp), v, *cid);
                    }
                    self.make_eliminating_clause(&mut (*tmp), v.lit(LTRUE));
                } else {
                    for cid in &pos {
                        self.make_eliminating_clause_(&mut (*tmp), v, *cid);
                    }
                    self.make_eliminating_clause(&mut (*tmp), v.lit(LFALSE));
                }
            }
            // Produce clauses in cross product via self.merge_vec:
            {
                let vec = &self.eliminator.merge_vec as *const Vec<Lit>;
                for p in &pos {
                    for n in &neg {
                        if self.merge(*p, *n, v) // && !self.add_clause_(&*vec) {
                        { self.add_learnt((*vec).clone());
                            // return false;
                        }
                    }
                }
            }
            for ci in &*cls {
                self.remove_clause(*ci);
            }
            // Free occurs list for this variable:
            // self.vars[v].occurs.clear();
            // FIXME I can't understand Glucose code!
            // Free watches lists for this variables, if possible:
            for ck in &[ClauseKind::Permanent, ClauseKind::Removable] {
                let cv = &self.cp[*ck as usize];
                if cv.watcher[v.lit(LTRUE) as usize] != 0 {
                    // watches[v.lit(true)].clear();
                }
                if cv.watcher[v.lit(LFALSE) as usize] != 0 {
                    // watches[v.lit(false)].clear();
                }
            }
            self.backward_subsumption_check()
        }
    }
    /// 18. eliminate
    // should be called at decision level 0.
    pub fn eliminate(&mut self, _: bool) -> () {
        // In Splr, this function is called from simplify_database
        // if !self.simplify_database() {
        //     self.ok = false;
        //     return false;
        // }
        // let target = &self.cp[ClauseKind::Removable as usize] as *const ClausePack;
        'perform: while 0 < self.eliminator.n_touched
            || self.eliminator.bwdsub_assigns < self.trail.len()
            || 0 < self.eliminator.heap.len()
        {
            let mut best_v = 1;
            for i in 2..self.vars.len() {
                if self.vars[best_v].num_occur < self.vars[i].num_occur {
                    best_v = i;
                }
            }
            self.vars[best_v].num_occur = 0;
            self.eliminator.best_v = best_v;
            self.gather_touched_clauses();
            {
                let target = &mut self.eliminator.subsumption_queue;
                if SUBSUMPTION_LIMIT < (*target).len() {
                    println!("Too many clauses to eliminate");
                    unsafe {
                        target.set_len(SUBSUMPTION_LIMIT);
                    }
                }
            }
            // println!("eliminate: start v {}, clauses {}, queue {}, {}, {}, {}",
            //          self.eliminator.best_v,
            //          self.cp[ClauseKind::Removable as usize].clauses.len(),
            //          self.eliminator.subsumption_queue.len(),
            //          0 < self.eliminator.n_touched,
            //          self.eliminator.bwdsub_assigns < self.trail.len(),
            //          0 < self.eliminator.heap.len(),
            // );
            // println!(" - queue {:?}", self.eliminator.subsumption_queue);
            if (0 < self.eliminator.subsumption_queue.len()
                || self.eliminator.bwdsub_assigns < self.trail.len())
                && !self.backward_subsumption_check()
            {
                println!("eliminate: break");
                self.ok = false;
                break 'perform; // goto cleaup
            }
            // abort after too long computation
            if false {
                break 'perform;
            }
            println!(" - heap: {:?}", self.eliminator.heap.len());
            while !self.eliminator.heap.is_empty() {
                let elim: VarId = self.vars.get_root(&mut self.eliminator.heap); // removeMin();
                                                                                 // if asynch_interrupt { break }
                if self.vars[elim].eliminated || self.vars[elim].assign != BOTTOM {
                    continue;
                }
                if self.eliminator.use_elim
                    && self.vars[elim].assign == BOTTOM
                    && self.vars[elim].frozen
                    && !self.eliminate_var(elim)
                {
                    self.ok = false;
                    break 'perform;
                }
            }
        }
    }
}

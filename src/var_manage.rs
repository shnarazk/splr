#![allow(dead_code)]
use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause_manage::ClauseManagement;
use solver::SatSolver;
use solver::SolverException::*;
use solver::SolverResult;
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use solver_rollback::Restart;
use types::*;
use var::Satisfiability;
use var::Var;
use var::VarIdHeap;
use var::VarOrdering;

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;

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

/// Literal eliminator
#[derive(Debug)]
pub struct Eliminator {
    merges: usize,
    /// renamed elimHeap. FIXME: can we use VarIdHeap here?
    heap: VarIdHeap,
    n_touched: usize,
    asymm_lits: usize,
    /// vector of numbers of occurences which contain a literal
    n_occ: Vec<Lit>,
    /// a mapping: VarIndex -> [ClauseId]
    occurs: Vec<Vec<ClauseId>>,
    subsumption_queue: Vec<ClauseId>,
    // eliminated: Vec<Var>,       // should be in Var?
    bwdsub_assigns: usize,
    bwdsub_tmp_unit: ClauseId,
    // working place
    merge_vec: Vec<Lit>,
    elim_clauses: Vec<Lit>,
    /// Variables are not eliminated if it produces a resolvent with a length above this limit.
    /// 0 means no limit.
    clause_lim: usize,
    eliminated_vars: usize,
    add_tmp: Vec<Lit>,
}

impl Eliminator {
    pub fn new(nv: usize) -> Eliminator {
        Eliminator {
            merges: 0,
            heap: VarIdHeap::new(nv + 1),
            n_touched: 0,
            asymm_lits: 0,
            n_occ: vec![0; nv + 1],
            occurs: vec![Vec::new(); nv + 1],
            subsumption_queue: Vec::new(),
            bwdsub_assigns: 0,
            bwdsub_tmp_unit: 0,
            merge_vec: vec![0; nv + 1],
            elim_clauses: vec![0; 2 * (nv + 1)],
            clause_lim: 20,
            eliminated_vars: 0,
            add_tmp: Vec::new(),
        }
    }
}

trait LiteralEliminator {
    fn asymm() -> bool;
    fn asymm_var() -> bool;
    fn update_elim_heap();
    fn gather_touched_clauses();
    fn merge(&self) -> bool;
    fn backward_subsumption_check() -> bool;
    fn eliminate_var(&self, vi: VarId) -> bool;
    fn extend_model(&self) -> ();
    fn remove_clause(&self, cid: ClauseId) -> ();
    fn strengthen_clause(&self, cid: ClauseId) -> bool;
    fn cleaup_clauses(&self) -> ();
    fn implied(&self, vec: &[Lit]) -> bool;
}

impl Solver {
    /// 2. solve_
    /// Note: Splr doesn't support 'assumption'.
    fn solve_(&mut self) -> SolverResult {
        match self.eliminate(false) {
            true => {
                let res = self.solve();
                if let Ok(_) = res {
                    self.extend_model();
                }
                res
            }
            false => Err(InternalInconsistent),
        }
    }
    /// 3. addClause
    pub fn add_clause_(&mut self, _vec: &[Lit]) -> bool {
        let nclauses = self.cp[ClauseKind::Permanent as usize].clauses.len();
        let cid = 0;
        if false {
            // FIXME: Solver::add_clause(vec);
            return false;
        }
        if nclauses == self.cp[ClauseKind::Permanent as usize].clauses.len() {
            return true;
        }
        let c = &iref!(self.cp, cid);
        self.eliminator.subsumption_queue.push(cid);
        for i in 0..c.len() {
            let l = lindex!(c, i);
            let vi = l.vi();
            self.eliminator.occurs[vi].push(cid);
            self.eliminator.n_occ[l as usize] += 1;
            self.vars[vi].touched = true;
            self.eliminator.n_touched += 1;
            self.eliminator.heap.update(&self.vars, vi);
        }
        true
    }
    /// 4. removeClause
    pub fn remove_clause(&mut self, cid: ClauseId) -> () {
        let Solver {
            ref cp,
            ref vars,
            ref mut eliminator,
            ..
        } = self;
        let c = iref!(cp, cid);
        for i in 0..c.lits.len() + 2 {
            let l = lindex!(c, i);
            eliminator.n_occ[l as usize] += 1;
            eliminator.update_heap(vars, l.vi());
            // occurs.smudge(l.vi());
        }
        // solver::removeClause(...)
    }
    /// 5. strengthenClause
    pub fn strengthen_clause(&mut self, cid: ClauseId, l: Lit) -> bool {
        let rank;
        let c0;
        let empty;
        {
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            self.eliminator.subsumption_queue.push(cid);
            if c.lits.is_empty() {
                empty = true; // substitute 'self.remove_clause(cid);'
                c.strengthen(l);
            } else {
                // detachClause(cid);
                c.strengthen(l);
                // attachClause(cid);
                // remove(occurs[var(l)], cid);
                self.eliminator.n_occ[l as usize] -= 1;
                self.eliminator.update_heap(&self.vars, l.vi());
                empty = false;
            }
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
        let Solver {
            ref mut cp,
            ref mut eliminator,
            ref mut vars,
            ..
        } = self;
        if eliminator.n_touched == 0 {
            return;
        }
        for cid in &eliminator.subsumption_queue {
            let c = &mut cp[cid.to_kind()].clauses[cid.to_index()];
            if !c.sve_mark {
                c.sve_mark = true;
            }
        }
        for vi in 1..vars.len() {
            if vars[vi].touched {
                let vec = &eliminator.occurs[vi];
                for cid in vec {
                    let c = &mut cp[cid.to_kind()].clauses[cid.to_index()];
                    if !c.sve_mark {
                        eliminator.subsumption_queue.push(*cid);
                        c.sve_mark = false;
                    }
                }
            }
            vars[vi].touched = false;
        }
        for cid in &eliminator.subsumption_queue {
            let c = &mut cp[cid.to_kind()].clauses[cid.to_index()];
            if c.sve_mark {
                c.sve_mark = false;
            }
        }
        eliminator.n_touched = 0;
    }
    /// 9. implied
    /// 全否定を試してみる？
    pub fn implied(&mut self, c: &[Lit]) -> bool {
        self.trail_lim.push(self.trail.len());
        for l in c {
            match self.assigned(*l) {
                LTRUE => {
                    self.cancel_until(0);
                    return false;
                }
                BOTTOM => self.uncheck_enqueue(l.negate(), NULL_CLAUSE),
                _ => (),
            }
        }
        let ret = self.propagate();
        self.cancel_until(0);
        ret != NULL_CLAUSE
    }
    /// 10. backwardSubsumptionCheck
    pub fn backward_subsumption_check(&self) -> bool {
        true
    }
    /// 11. asymm
    pub fn asymm(&mut self, vi: VarId, cid: ClauseId) -> bool {
        let mut lit: Lit = NULL_LIT;
        unsafe {
            let c = &self.cp[cid.to_kind()].clauses[cid.to_index()] as *const Clause;
            if (*c).sve_mark || self.vars.satisfies(&*c) {
                return true;
            }
            self.trail_lim.push(self.trail.len());
            for i in 0..(*c).len() {
                let l = lindex!(*c, i);
                if l.vi() != vi && self.vars.assigned(l) != LFALSE {
                    self.uncheck_enqueue(l.negate(), NULL_CLAUSE);
                } else {
                    lit = l;
                }
            }
        }
        if self.propagate() != NULL_CLAUSE {
            self.eliminator.asymm_lits += 1;
            self.cancel_until(0);
            if !self.strengthen_clause(cid, lit) {
                return false;
            }
        } else {
            self.cancel_until(0);
        }
        true
    }
    /// 12. asymmVar
    pub fn asymm_var(&mut self, vi: VarId) -> bool {
        if self.vars[vi].assign != BOTTOM || self.eliminator.occurs[vi].len() == 0 {
            return true;
        }
        unsafe {
            let cv = &self.eliminator.occurs[vi] as *const Vec<ClauseId>;
            for cid in &*cv {
                if !self.asymm(vi, *cid) {
                    return false;
                }
            }
        }
        self.backward_subsumption_check()
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
        unsafe {
        let cls = &self.eliminator.occurs[v] as *const Vec<ClauseId>;
        let mut pos: Vec<ClauseId> = Vec::new();
        let mut neg: Vec<ClauseId> = Vec::new();
        // Split the occurrences into positive and negative:
        for cid in &*cls {
            let c = &self.cp[cid.to_kind()].clauses[cid.to_index()];
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
                if  res {
                    cnt += 1;
                    if (*cls).len() < cnt || (self.eliminator.clause_lim != 0 && self.eliminator.clause_lim < clause_size) {
                        return true;
                    }
                }
            }
        }
        // Delete and store old clauses
        self.vars[v].eliminated = true;
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
                        if self.merge(*p, *n, v) && !self.add_clause_(&*vec) {
                            return false;
                        }
                    }
                }
        }
        for ci in &*cls {
            self.remove_clause(*ci);
        }
        // Free occurs list for this variable:
        self.eliminator.occurs[v].clear();
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
    /// 16. substitute
    pub fn substitute(&mut self, vi: VarId, x: Lit) -> bool {
        if !self.ok {
            return false;
        }
        self.vars[vi].eliminated = true;
        // setDecisionVar(v, false);
        unsafe {
        let cls = &self.eliminator.occurs[vi] as *const Vec<ClauseId>;
        let subst_clause = &mut self.eliminator.add_tmp as *mut Vec<Lit>;
        for ci in &*cls {
            (*subst_clause).clear();
            let c = &self.cp[ci.to_kind()].clauses[ci.to_index()] as *const Clause;
            for i in 0..(*c).len() {
                let p = lindex!((*c), i);
                if p.vi() == vi {
                    if p.positive() {
                        (*subst_clause).push(x);
                    } else {
                        (*subst_clause).push(x.negate());
                    }
                } else {
                        (*subst_clause).push(p);
                }
            }
            if !self.add_clause_(&*subst_clause) {
                self.ok = false;
                return false;
            }
            self.remove_clause(*ci);
        }
        }
        true
    }
    /// 17. extendModel
    /// ```c
    /// inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
    /// inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
    /// ```
    pub fn extend_model(&mut self) -> () {
        if self.model.len() == 0 {
            unsafe {
                let nv = self.vars.len();
                self.model.reserve(nv);
                self.model.set_len(nv);
            }
        }
        let mut i = self.eliminator.elim_clauses.len() - 1;
        let mut j;
        'next: loop {
                j = self.eliminator.elim_clauses[i] as usize;
                i -= 1;
            loop {
                if j <= 1 {
                    break;
                }
                let model_value = match (self.eliminator.elim_clauses[i].positive(), self.vars[self.eliminator.elim_clauses[i].vi()].assign) {
                    (true, x) => x,
                    (false, x) => negate_bool(x),
                };
                if model_value != LFALSE {
                    i -= j;
                    continue 'next;
                }
                j -= 1;
                i -= 1;
            }
            let l = self.eliminator.elim_clauses[i];
            self.model[l.vi()] = if l.positive() { LFALSE } else { LTRUE };
            i -= j;
        }
    }
    /// 18. eliminate
    pub fn eliminate(&mut self, _: bool) -> bool {
        let result = {
            self.simplify_database();
            true
        };
        if !result {
            self.ok = false;
            return false;
        }
        self.ok
    }
    /// 19. cleanUpClauses
    pub fn cleanup_clauses(&self) -> () {
        // FIXME occurs.cleanAll();
        // FIXME self.cv.drain(|c| c.mark);
    }
    /// 20. relocAll
    pub fn reloc_all(&self) -> () {}
    /// 21. garbageCollect
    pub fn garbage_collect(&self) -> () {}
    // is_eliminated(vi) == self.vars[vi].eliminated
}

impl Eliminator {
    // from SimpSolver.h update_elim_heap
    pub fn update_heap(&mut self, vars: &[Var], vi: VarId) -> () {
        let v = &vars[vi];
        if self.heap.contains(vi) || (v.frozen && vars[vi].eliminated && v.assign == BOTTOM) {
            self.heap.update(vars, vi);
        }
    }
    // is_eliminated(vi) == self.vars[vi].eliminated
}

impl Clause {
    /// remove Lit `p` from Clause *self*.
    pub fn strengthen(&mut self, _p: Lit) -> () {
        // FIXME
    }
}

// class Clause {
//     void calcAbstraction() {
//         assert(header.extra_size > 0);
//         uint32_t abstraction = 0;
//         for (int i = 0; i < size(); i++)
//             abstraction |= 1 << (var(data[i].lit) & 31);
//         data[header.size].abs = abstraction;  }
// }
//  inline void Clause::strengthen(Lit p)
//  {
//      remove(*this, p);
//      calcAbstraction();
//  }

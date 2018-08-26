#![allow(dead_code)]
use clause::ClauseKind;
use clause::ClauseIdIndexEncoding;
use solver::SatSolver;
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use types::*;
use var::VarIndexHeap;
use var::VarOrdering;
use solver_rollback::Restart;
use clause_manage::ClauseManagement;
use solver::SolverResult;
use solver::SolverException::*;

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;

pub trait VarSelect {
    fn select_var(&mut self) -> VarIndex;
    fn bump_vi(&mut self, vi: VarIndex) -> ();
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
    fn bump_vi(&mut self, vi: VarIndex) -> () {
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
    fn select_var(&mut self) -> VarIndex {
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
    /// renamed elimHeap
    /// FIXME: can we use VarIndexHeap here?
    heap: VarIndexHeap,
    n_touched: usize,
    /// vector of numbers of occurences which contain a literal
    n_occ: Vec<Lit>,
    occurs: Vec<Vec<ClauseId>>,
    subsumption_queue: Vec<ClauseId>,
    // frozen: Vec<Var>,           // should be in Var
    // eliminated: Vec<Var>,       // should be in VarIndexHeap
    bwdsub_assigns: usize,
    bwdsub_tmpunit: ClauseId,
    // working place
    merge_vec: Vec<Lit>,
    elim_clauses: Vec<Lit>,
}

impl Eliminator {
    pub fn new(nv: usize) -> Eliminator {
        Eliminator {
            merges: 0,
            heap: VarIndexHeap::new(nv + 1),
            n_touched: 0,
            n_occ: vec![0; nv + 1],
            occurs: vec![Vec::new(); nv + 1],
            subsumption_queue: Vec::new(),
            bwdsub_assigns: 0,
            bwdsub_tmpunit: 0,
            merge_vec: vec![0; nv + 1],
            elim_clauses: vec![0; 2 * (nv + 1)],
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
    fn eliminate_var(&self, vi: VarIndex) -> bool;
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
    pub fn add_clause__(&mut self, _vec: &[Lit]) -> bool {
        let nclauses = self.cp[ClauseKind::Permanent as usize].clauses.len();
        let cid = 0;
        if false {   // FIXME: Solver::add_clause(vec);
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
        let c = iref!(self.cp, cid);
        for i in 0..c.lits.len() + 2 {
            let l = lindex!(c, i);
            self.eliminator.n_occ[l as usize] += 1;
            // update_elim_heap(l.vi());
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
            let c = &self.cp[cid.to_kind()].clauses[cid.to_index()];
            self.eliminator.subsumption_queue.push(cid);
            if c.lits.is_empty() {
                empty = true; // substitute 'self.remove_clause(cid);'
            // c.strengthen(l);
            } else {
                // detachClause(cid);
                // c.strengthen(l);
                // attachClause(cid);
                // remove(occurs[var(l)], cid);
                self.eliminator.n_occ[l as usize] -= 1;
                // update_elim_heap(l.vi());
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
    /// 6. merge
    /// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
    pub fn merge(&mut self, cp: ClauseId, cq: ClauseId, v: VarIndex) -> bool {
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
    /// 7. merge
    /// Returns **false** if one of the clauses is always satisfied.
    pub fn merge_(&mut self, cp: ClauseId, cq: ClauseId, v: VarIndex) -> (bool, usize) {
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
    pub fn gather_touched_clauses(&self) -> () {
        if self.eliminator.n_touched == 0 {
            return;
        }
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
    pub fn asymm(&self, _vi: VarIndex, _ci: ClauseId) -> bool {
        true
    }
    /// 12. asymmVar
    pub fn asymm_var(&self, _vi: VarIndex) -> bool {
        true
    }
    /// 13. mkElimClause
    pub fn make_eliminating_clause(&self, mut vec: Vec<Lit>, x: Lit) -> () {
        vec.push(x);
        vec.push(1);
    }
    /// 14. mkElimClause
    pub fn make_eliminating_clause_(&self, _vec: Vec<Lit>, _vi: VarIndex, _ci: ClauseId) -> () {
        
    }
    /// 15. eliminateVar
    pub fn eliminate_var(&self, _vi: VarIndex) -> bool {
        true
    }
    /// 16. substitute
    pub fn substitute(&self, _vi: VarIndex, _x: Lit) -> bool {
        true
    }
    /// 17. extendModel
    pub fn extend_model(&self) -> () {}
    /// 18. eliminate
    pub fn eliminate(&mut self, _: bool) -> bool {
        let result = { self.simplify_database(); true };
        if !result {
            self.ok = false;
            return false;
        }
        self.ok
    }
    /// 19. cleanUpClauses
    pub fn cleanup_clauses(&self) -> () {
    }
    /// 20. relocAll
    pub fn reloc_all(&self) -> () {
    }
    /// 21. garbageCollect
    pub fn garbage_collect(&self) -> () {
    }
}

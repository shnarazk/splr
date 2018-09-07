#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_imports)]
use clause::Clause;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause::ClausePack;
use clause::CLAUSE_KINDS;
use clause::DEAD_CLAUSE;
use clause_manage::ClauseManagement;
use clause_manage::KINDS;
use solver::SatSolver;
use solver::SolverException::*;
use solver::SolverResult;
use solver::{Solver, Stat};
use solver_propagate::SolveSAT;
use solver_rollback::Restart;
use std::cmp::Ordering;
use std::ops::Neg;
use types::*;
use var::AccessHeap;
use var::Eliminator;
use var::Satisfiability;
use var::Var;
use var::VarIdHeap;
use var::VarOrder;
use var::VarOrdering;

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;
const SUBSUMPITON_GROW_LIMIT: usize = 0;
const SUBSUMPTION_VAR_QUEUE_MAX: usize = 10_000;
const SUBSUMPTION_CLAUSE_QUEUE_MAX: usize = 10_000;
const SUBSUMPTION_COMBINATION_MAX: usize = 10_000_000;

pub trait VarSelect {
    fn select_var(&mut self) -> VarId;
    fn bump_vi(&mut self, vi: VarId) -> ();
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
        }
        self.var_order.update(&self.vars, vi);
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
    /// 3. addClause
    /// - calls `enqueue_clause`
    pub fn add_cross(&mut self, vec: Vec<Lit>) -> bool {
        if vec.len() == 1 {
            self.enqueue(vec[0], NULL_CLAUSE);
            return true;
        }
        let nclauses = self.cp[ClauseKind::Permanent as usize].clauses.len();
        let cid = self.attach_clause(Clause::new(ClauseKind::Permanent, false, vec.len(), vec));
        debug_assert_ne!(nclauses, cid);
        // if nclauses == cid {
        //     return true;
        // }
        // println!("add cross clause {}:{}", cid.to_kind(), cid.to_index());
        let c = &iref!(self.cp, cid);
        self.eliminator.enqueue_clause(cid);
        for i in 0..c.len() {
            let l = lindex!(c, i);
            let mut v = &mut self.vars[l.vi()];
            v.touched = true;
            self.eliminator.n_touched += 1;
            if !v.eliminated && v.elimination_target {
                if l.positive() {
                    v.pos_occurs.push(cid);
                } else {
                    v.neg_occurs.push(cid);
                }
            }
        }
        true
    }
    /// 4. removeClause
    /// called from strengthen_clause, backward_subsumption_check, eliminate_var, substitute
    /// - calls `enqueue_var`
    pub fn remove_clause(&mut self, cid: ClauseId) -> () {
        let Solver {
            ref mut cp,
            ref mut vars,
            ref mut eliminator,
            ..
        } = self;
        let mut c = &mut cp[cid.to_kind()].clauses[cid.to_index()];
        for i in 0..c.len() {
            let l = lindex!(c, i);
            let vi = l.vi();
            if vars[vi].elimination_target {
                if l.positive() {
                    vars[vi].pos_occurs.retain(|&ci| ci != cid);
                } else {
                    vars[vi].neg_occurs.retain(|&ci| ci != cid);
                }
                eliminator.enqueue_var(vi);
            }
        }
        // println!("     purge {} by remove_clause", cid.to_index());
        c.index = DEAD_CLAUSE;
    }
    /// 5. strengthenClause
    /// - calls `enqueue_clause`
    /// - calls `enqueue_var`
    pub fn strengthen_clause(&mut self, cid: ClauseId, l: Lit) -> bool {
        // println!("STRENGTHEN_CLAUSE {}", cid.to_index());
        let c0;
        {
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            debug_assert_ne!(cid, NULL_CLAUSE);
            self.eliminator.enqueue_clause(cid);
            if c.lits.is_empty() {
                c.strengthen(l);
                c0 = c.lit[0];
            } else {
                c.strengthen(l);
                if l.positive() {
                    self.vars[l.vi()].pos_occurs.retain(|&ci| ci != cid);
                } else {
                    self.vars[l.vi()].neg_occurs.retain(|&ci| ci != cid);
                }
                if self.vars[l.vi()].elimination_target {
                    self.eliminator.enqueue_var(l.vi());
                }
                c0 = NULL_LIT;
            }
        }
        if c0 != NULL_LIT {
            self.remove_clause(cid);
            // FIXME I need to call garbage_collect??
            // self.rebuild_watchers(CLAUSE_KINDS[cid.to_kind() as usize]);
            // // println!("STRENGTHEN_CLAUSE ENQUEUE {}", c0);
            // self.rebuild_watchers(ClauseKind::Removable);
            // self.rebuild_watchers(ClauseKind::Permanent);
            // self.rebuild_watchers(ClauseKind::Binclause);
            self.enqueue(c0, NULL_CLAUSE) && self.propagate() == NULL_CLAUSE
        } else {
            true
        }
    }
    /// 6. merge(1)
    /// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
    pub fn merge(&mut self, cp: ClauseId, cq: ClauseId, v: VarId) -> Option<Vec<Lit>> {
        let mut vec: Vec<Lit> = Vec::new();
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
                            return None;
                        } else {
                            continue 'next_literal;
                        }
                    }
                }
                vec.push(l);
            }
        }
        for i in 0..p.len() {
            let l = lindex!(p, i);
            if l.vi() != v {
                vec.push(l);
            }
        }
        // println!("merge generated {:?} from {} and {} to eliminate {}", vec2int(vec.clone()), p, q, v);
        Some(vec)
    }
    /// 7. merge(2)
    /// Returns **false** if one of the clauses is always satisfied.
    pub fn check_to_merge(&mut self, cp: ClauseId, cq: ClauseId, v: VarId) -> (bool, usize) {
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
    /// remove all vars which have a single positive or negative occurence.
    pub fn build_binary_occurrence(&mut self) -> () {
        for v in &mut self.vars[1..] {
            v.bin_pos_occurs.clear();
            v.bin_neg_occurs.clear();
        }
        for c in &self.cp[ClauseKind::Binclause as usize].clauses[1..] {
            if c.index == DEAD_CLAUSE {
                debug_assert!(c.dead);
                continue;
            }
            for l in c {
                let v = &mut self.vars[l.vi()];
                if l.positive() {
                    v.bin_pos_occurs.push(ClauseKind::Binclause.id_from(c.index));
                } else {
                    v.bin_neg_occurs.push(ClauseKind::Binclause.id_from(c.index));
                }
            }
        }
    }
    /// remove all vars which have a single positive or negative occurence.
    pub fn eliminate_unit_vars(&mut self) -> () {
        for v in &mut self.vars[1..] {
            v.elimination_target = !v.eliminated && v.assign == BOTTOM;
            v.pos_occurs.clear();
            v.neg_occurs.clear();
        }
        // We can ignore learnt caluses because they are logical consequences from the problem.
        for ck in &[ClauseKind::Permanent, ClauseKind::Binclause] {
            let target = &self.cp[*ck as usize].clauses;
            for c in &target[1..] {
                for l in c {
                    let v = &mut self.vars[l.vi()];
                    if v.elimination_target {
                        if 1 < v.pos_occurs.len() && 1 < v.neg_occurs.len() {
                            v.elimination_target = false;
                            v.pos_occurs.clear();
                            v.neg_occurs.clear();
                        } else if l.positive() {
                            v.pos_occurs.push(ck.id_from(c.index));
                        } else {
                            v.neg_occurs.push(ck.id_from(c.index));
                        }
                    }
                }
            }
        }
        let mut cnt = 0;
        for v in &self.vars[1..] {
            if v.elimination_target && (v.pos_occurs.len() == 1 || v.neg_occurs.len() == 1) {
                self.eliminator.enqueue_var(v.index);
                cnt += 1;
            }
        }
        println!("#elim, num vars, {}", cnt);
    }
    /// 8. gatherTouchedClauses
    /// - calls `enqueue_clause`
    pub fn gather_touched_clauses(&mut self) -> () {
        if self.eliminator.n_touched == 0 {
            return;
        }
        let mut len = self.eliminator.clause_queue.len();
        for cid in &self.eliminator.clause_queue {
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            c.touched = true;
        }
        for mut v in &mut self.vars[1..] {
            if v.touched && v.elimination_target {
                // println!("gtc var: {}", v.index);
                for cid in &v.pos_occurs {
                    let mut c = mref!(self.cp, cid);
                    if !c.touched {
                        self.eliminator.enqueue_clause(*cid);
                        c.touched = true;
                    }
                }
                for cid in &v.neg_occurs {
                    let mut c = mref!(self.cp, cid);
                    if !c.touched {
                        self.eliminator.enqueue_clause(*cid);
                        c.touched = true;
                    }
                }
                v.touched = false;
            }
        }
        // println!("gather_touched_classes: clause_queue {}", self.eliminator.clause_queue.len());
        for cid in &self.eliminator.clause_queue {
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            c.touched = false;
        }
        for v in &mut self.vars {
            v.touched = false;
        }
        self.eliminator.n_touched = 0;
    }
    /// 10. backwardSubsumptionCheck
    /// - calls `clause_queue.pop`
    pub fn backward_subsumption_check(&mut self) -> bool {
        let mut cnt = 0;
        let mut subsumed = 0;
        let mut deleted_literals = 0;
        debug_assert_eq!(self.decision_level(), 0);
        while 0 < self.eliminator.clause_queue.len()
            || self.eliminator.bwdsub_assigns < self.trail.len()
        {
            // Empty subsumption queue and return immediately on user-interrupt:
            // if computed-too-long { break; }
            // Check top-level assigments by creating a dummy clause and placing it in the queue:
            if self.eliminator.clause_queue.len() == 0
                && self.eliminator.bwdsub_assigns < self.trail.len()
            {
                let l: Lit = self.trail[self.eliminator.bwdsub_assigns];
                let id = self.eliminator.bwdsub_tmp_clause.index;
                self.eliminator.bwdsub_assigns += 1;
                self.eliminator.bwdsub_tmp_clause.lit[0] = l;
                self.eliminator.enqueue_clause(id);
            }
            let cid = self.eliminator.clause_queue[0];
            self.eliminator.clause_queue.remove(0);
            unsafe {
                let mut c = if cid == self.eliminator.bwdsub_tmp_clause.index {
                    &mut self.eliminator.bwdsub_tmp_clause as *mut Clause
                } else {
                    &mut self.cp[cid.to_kind()].clauses[cid.to_index()] as *mut Clause
                };
                if (*c).sve_mark || (*c).index == DEAD_CLAUSE {
                    continue;
                }
                // println!("check with {} for best_v {}", *c, self.eliminator.best_v);
                debug_assert!(1 < (*c).len() || self.vars.assigned((*c).lit[0]) == LTRUE);
                // unit clauses should have been propagated before this point.
                // Find best variable to scan:
                let mut best = 0;
                let mut tmp = 0;
                'next_var: for i in 0..(*c).len() {
                    let l = lindex!(*c, i);
                    let v = &self.vars[l.vi()];
                    // println!("select var {}, {}, {}", l.vi(), v.elimination_target, v.occurs.len());
                    if v.elimination_target && tmp < v.pos_occurs.len() + v.neg_occurs.len() {
                        best = l.vi();
                        tmp = v.pos_occurs.len() + v.neg_occurs.len();
                    }
                }
                // println!("select var {}", best);
                if best == 0 {
                    continue;
                }
                // Search all candidates:
                for cs in &[
                    &mut self.vars[best].pos_occurs as *mut Vec<ClauseId>,
                    &mut self.vars[best].neg_occurs as *mut Vec<ClauseId>,
                ] {
                    // let cs = &mut self.vars[best].pos_occurs as *mut Vec<ClauseId>;
                    for di in &mut **cs {
                        let d = &self.cp[di.to_kind()].clauses[di.to_index()] as *const Clause;
                        if (!(*d).sve_mark || (*d).index != DEAD_CLAUSE)
                            && *di != cid
                            && (*c).len() <= self.eliminator.subsume_clause_size
                            && (*d).len() <= self.eliminator.subsume_clause_size
                            && (self.eliminator.subsumption_lim == 0
                                || (*c).len() + (*d).len() <= self.eliminator.subsumption_lim)
                        // && (self.eliminator.subsumption_lim == 0 || (*d).len() < self.eliminator.subsumption_lim)
                        {
                            // println!("{} + {}", *c, *d);
                            match (*c).subsumes(&*d) {
                                Some(NULL_LIT) => {
                                    // println!("    => {} subsumed completely by {}", *d, *c);
                                    subsumed += 1;
                                    self.remove_clause(*di);
                                }
                                Some(l) => {
                                    // println!("    => subsumed {} from {} and {}", l.int(), *c, *d);
                                    deleted_literals += 1;
                                    if !self.strengthen_clause(*di, l.negate()) {
                                        return false;
                                    }
                                }
                                None => {}
                            }
                        }
                    }
                }
                self.eliminator.targets.clear();
            }
        }
        true
    }
    /// 10. backwardSubsumptionCheck
    /// - calls `clause_queue.pop`
    pub fn binary_subsumption_check(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        unsafe {
            while let Some(cid) = self.eliminator.binclause_queue.pop() {
                if cid.to_kind() != ClauseKind::Binclause as usize {
                    continue;
                }
                let c = &mut self.cp[ClauseKind::Binclause as usize].clauses[cid.to_index()] as *mut Clause;
                if (*c).sve_mark || (*c).index == DEAD_CLAUSE {
                    continue;
                }
                for i in 0..2 {
                    let l = (*c).lit[i];
                    if self.vars[l.vi()].eliminated {
                        continue;
                    }
                    let targets = if l.positive() {
                        &mut self.vars[l.vi()].bin_neg_occurs as *mut Vec<ClauseId>
                    } else {
                        &mut self.vars[l.vi()].bin_pos_occurs as *mut Vec<ClauseId>
                    };
                    for did in &*targets {
                        if *did == DEAD_CLAUSE {
                            continue;
                        }
                        debug_assert_eq!(did.to_kind(), ClauseKind::Binclause as usize);
                        // println!("check with {} for best_v {}", *c, self.eliminator.best_v);
                        // Search all candidates:
                        let d = &mut self.cp[ClauseKind::Binclause as usize].clauses[did.to_index()] as *mut Clause;
                        if (*d).index != DEAD_CLAUSE && (*d).index != (*c).index {
                            // println!("{} + {}", *c, *d);
                            match (*c).subsumes(&*d) {
                                Some(NULL_LIT) => {
                                    println!("    => {} subsumed completely by {}", *d, *c);
                                    self.remove_clause(*did);
                                }
                                Some(l) => {
                                    println!("    => subsumed {} from {} and {}", l.int(), *c, *d);
                                    if !self.strengthen_clause(*did, l.negate()) {
                                        return false;
                                    }
                                }
                                None => {}
                            }
                        }
                    }
                }
            }
        }
        true
    }
    /// 13. mkElimClause(1)
    pub fn make_eliminating_unit_clause(&self, vec: &mut Vec<Lit>, x: Lit) -> () {
        vec.push(x);
        vec.push(1);
    }
    /// 14. mkElimClause(2)
    pub fn make_eliminated_clause(&self, vec: &mut Vec<Lit>, vi: VarId, cid: ClauseId) -> () {
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
        // Store the length of the clause last:
        vec.push(c.len() as u32);
    }
    /// 15. eliminateVar
    pub fn eliminate_var(&mut self, v: VarId) -> bool {
        debug_assert!(!self.vars[v].eliminated);
        if !self.vars[v].elimination_target {
            return true;
        }
        unsafe {
            let mut pos = &mut self.vars[v].pos_occurs as *mut Vec<ClauseId>;
            let mut neg = &mut self.vars[v].neg_occurs as *mut Vec<ClauseId>;
            // Check wether the increase in number of clauses stays within the allowed ('grow').
            // Moreover, no clause must exceed the limit on the maximal clause size (if it is set).
            if 1 < (*pos).len() && 1 < (*neg).len() {
                let clslen = (*pos).len() + (*neg).len();
                let mut cnt = 0;
                for i in 0..(*pos).len() {
                    for j in 0..(*neg).len() {
                        let (res, clause_size) = self.check_to_merge((*pos)[i], (*neg)[j], v);
                        if res {
                            cnt += 1;
                            if clslen + SUBSUMPITON_GROW_LIMIT < cnt
                                || (self.eliminator.clause_lim != 0
                                    && self.eliminator.clause_lim < clause_size)
                            {
                                return true;
                            }
                        }
                    }
                }
            }
            // Delete and store old clauses
            self.vars[v].eliminated = true;
            // println!(
            //     "- eliminate_var: {:>5} (+{:<4} -{:<4})",
            //     v,
            //     pos.len(),
            //     neg.len()
            // );
            // setDecisionVar(v, false);
            self.eliminator.eliminated_vars += 1;
            {
                let tmp = &mut self.eliminator.elim_clauses as *mut Vec<Lit>;
                if (*neg).len() < (*pos).len() {
                    for cid in &*neg {
                        self.make_eliminated_clause(&mut (*tmp), v, *cid);
                    }
                    self.make_eliminating_unit_clause(&mut (*tmp), v.lit(LTRUE));
                } else {
                    for cid in &*pos {
                        self.make_eliminated_clause(&mut (*tmp), v, *cid);
                    }
                    self.make_eliminating_unit_clause(&mut (*tmp), v.lit(LFALSE));
                }
            }
            // Produce clauses in cross product via self.merge_vec:
            {
                for p in &*pos {
                    for n in &*neg {
                        if let Some(vec) = self.merge(*p, *n, v) {
                            if !self.add_cross(vec) {
                                return false;
                            }
                        }
                    }
                }
            }
            let cis = &self.vars[v].pos_occurs as *const Vec<ClauseId>;
            for ci in &*cis {
                self.remove_clause(*ci);
            }
            self.vars[v].pos_occurs.clear();
            let cis = &self.vars[v].neg_occurs as *const Vec<ClauseId>;
            for ci in &*cis {
                self.remove_clause(*ci);
            }
            self.vars[v].neg_occurs.clear();
            self.backward_subsumption_check()
        }
    }
    /// 17. extendModel
    /// ```c
    /// inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
    /// inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
    /// ```
    pub fn extend_model(&mut self, model: &mut Vec<i32>) -> () {
        // println!("extend_model: from {:?}", self.eliminator.elim_clauses);
        if self.eliminator.elim_clauses.is_empty() {
            return;
        }
        let mut i = self.eliminator.elim_clauses.len() - 1;
        let mut width;
        'next: loop {
            width = self.eliminator.elim_clauses[i] as usize;
            if width == 0 && i == 0 {
                break;
            }
            i -= 1;
            loop {
                if width <= 1 {
                    break;
                }
                let l = self.eliminator.elim_clauses[i];
                let model_value = match model[l.vi() - 1] {
                    x if x == l.int() => LTRUE,
                    x if -x == l.int() => LFALSE,
                    _ => BOTTOM,
                };
                if model_value != LFALSE {
                    if i < width {
                        break 'next;
                    }
                    i -= width;
                    continue 'next;
                }
                width -= 1;
                i -= 1;
            }
            let l = self.eliminator.elim_clauses[i];
            // println!(" - fixed {}", l.int());
            model[l.vi() - 1] = l.int(); // .neg();
            if i < width {
                break;
            }
            i -= width;
        }
    }
    /// 18. eliminate
    // should be called at decision level 0.
    pub fn eliminate(&mut self) -> () {
        self.eliminator.var_queue.clear();
        self.eliminator.clause_queue.clear();
        self.eliminate_unit_vars();
        // for i in 1..4 { println!("eliminate report: v{} => {},{}", i, self.vars[i].num_occurs, self.vars[i].occurs.len()); }
        'perform: while 0 < self.eliminator.n_touched
            || self.eliminator.bwdsub_assigns < self.trail.len()
            || 0 < self.eliminator.var_queue.len()
        {
            self.gather_touched_clauses();
            if (0 < self.eliminator.clause_queue.len()
                || self.eliminator.bwdsub_assigns < self.trail.len())
                && !self.backward_subsumption_check()
            {
                self.ok = false;
                break 'perform; // goto cleaup
            }
            while !self.eliminator.var_queue.is_empty() {
                let elim = self.eliminator.var_queue.remove(0);
                if self.vars[elim].eliminated
                    || self.vars[elim].assign != BOTTOM
                    || !self.vars[elim].elimination_target
                {
                    continue;
                }
                if !self.eliminate_var(elim) {
                    self.ok = false;
                    break 'perform;
                }
            }
        }
    }
    pub fn eliminate_binclauses(&mut self) -> () {
        println!("#bice, targets: {}", self.eliminator.binclause_queue.len());
        if !self.eliminator.binclause_queue.is_empty() {
            self.build_binary_occurrence();
            self.binary_subsumption_check();
        }
    }
}

impl Eliminator {
    fn enqueue_var(&mut self, vi: VarId) -> bool {
        if None == self.var_queue.iter().find(|&v| *v == vi) {
            if self.var_queue.len() < SUBSUMPTION_VAR_QUEUE_MAX {
                self.var_queue.push(vi);
                false
            } else {
                true
            }
        } else {
            false
        }
    }
    fn enqueue_clause(&mut self, ci: ClauseId) -> bool {
        if None == self.clause_queue.iter().find(|&i| *i == ci) {
            if self.clause_queue.len() < SUBSUMPTION_CLAUSE_QUEUE_MAX {
                self.clause_queue.push(ci);
                false
            } else {
                true
            }
        } else {
            false
        }
    }
}

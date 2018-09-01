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
use var::Satisfiability;
use var::Var;
use var::VarIdHeap;
use var::VarOrder;
use var::VarOrdering;

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;
const GROW: usize = 0;
const SUBSUMPTION_QUEUE_MAX: usize = 800_000;
const SUBSUMPTION_COMBINATION_MAX: usize = 1_000_000;

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
    /// 3. addClause
    pub fn add_cross(&mut self, vec: Vec<Lit>) -> bool {
        let nclauses = self.cp[ClauseKind::Permanent as usize].clauses.len();
        let cid = self.attach_clause(Clause::new(ClauseKind::Permanent, false, vec.len(), vec));
        if nclauses == cid {
            return true;
        }
        // println!("add cross clause {}:{}", cid.to_kind(), cid.to_index());
        let c = &iref!(self.cp, cid);
        // println!("cid {} {:?}", cid.to_index(), c);
        self.eliminator.subsumption_queue.push(cid);
        let big = c.len() < self.eliminator.subsume_clause_size;
        for i in 0..c.len() {
            let l = lindex!(c, i);
            let mut v = &mut self.vars[l.vi()];
            v.touched = true;
            self.eliminator.n_touched += 1;
            if big {
                v.terminal = false;
                v.occurs.clear();
            } else if v.terminal {
                    v.occurs.push(cid);
            }
        }
        true
    }
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
        if c.len() <= eliminator.subsume_clause_size {
            for i in 0..c.lits.len() + 2 {
                let vi = lindex!(c, i).vi();
                if 0 < vars[vi].occurs.len() {
                    vars[vi].occurs.retain(|&ci| ci != cid);
                }
                eliminator.heap.insert(vars, vi);
            }
        }
        // println!("     purge {} by remove_clause", cid.to_index());
        c.index = DEAD_CLAUSE;
    }
    /// 5. strengthenClause
    pub fn strengthen_clause(&mut self, cid: ClauseId, l: Lit) -> bool {
        // println!("STRENGTHEN_CLAUSE {}", cid.to_index());
        let c0;
        {
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            debug_assert_ne!(cid, NULL_CLAUSE);
            self.eliminator.subsumption_queue.push(cid);
            if c.lits.is_empty() {
                c.strengthen(l);
                c0 = c.lit[0];
            } else {
                c.strengthen(l);
                self.vars[l.vi()].occurs.retain(|&ci| ci != cid);
                self.eliminator.heap.insert(&self.vars, l.vi());
                c0 = NULL_LIT;
            }
        }
        if c0 != NULL_LIT {
            self.remove_clause(cid);
            self.rebuild_watchers(CLAUSE_KINDS[cid.to_kind() as usize]);
            // println!("STRENGTHEN_CLAUSE ENQUEUE {}", c0);
            self.rebuild_watchers(ClauseKind::Removable);
            self.rebuild_watchers(ClauseKind::Permanent);
            self.rebuild_watchers(ClauseKind::Binclause);
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
    /// finds small and complete clauses sets to eliminate variables soundly, even if a given formula is big.
    /// 1. determine the maximum size of clauses which contain the variable, for all variables.
    /// 2. collect 'small' variables and collect their corresponding clouses.
    pub fn build_occurence_list(&mut self) -> () {
        for i in 1..self.vars.len() {
            self.vars[i].terminal = true;
            self.vars[i].max_clause_size = 0;
            self.vars[i].num_occurs = 0;
            self.vars[i].occurs.clear();
        }
        for ck in &CLAUSE_KINDS[0..3] {
            let clauses = &self.cp[*ck as usize].clauses;
            for i in 1..clauses.len() {
                let c = &clauses[i];
                if c.index == DEAD_CLAUSE {
                    continue;
                }
                let len = c.len();

                if self.eliminator.subsume_clause_size < len {
                    for j in 0..len {
                        let l = lindex!(c, j);
                        self.vars[l.vi()].terminal = false;
                        self.vars[l.vi()].occurs.clear();
                    }
                } else {
                    for j in 0..len {
                        let l = lindex!(c, j);
                        let v = &mut self.vars[l.vi()];
                        v.max_clause_size = v.max_clause_size.max(len);
                        v.num_occurs += 1;
                    }
                }
            }
        }
        let mut targets: Vec<(usize, isize, usize)> = (1..self.vars.len())
            .map(|i| (self.vars[i].max_clause_size, (self.vars[i].num_occurs as isize).neg(), i)).collect();
        targets.sort();
        let mut end = 0;
        let mut total = 0;
        for k in 0..targets.len() {
            total += targets[k].1.neg() as usize;
            if 10 < total {
                end = k;
                break;
            }
        }
        let targets: Vec<VarId> = targets.drain(..end).map(|c| c.2).collect();
        for v in &mut self.vars {
            v.terminal = false;
            v.num_occurs = 0;
            v.occurs.clear();
        }
        for vi in &targets {
            self.vars[*vi].terminal = true;
        }
        for ck in &CLAUSE_KINDS[0..3] {
            let clauses = &self.cp[*ck as usize].clauses;
            for i in 1..clauses.len() {
                let c = &clauses[i];
                if c.index == DEAD_CLAUSE {
                    continue;
                }
                for j in 0..c.len() {
                    let l = lindex!(c, j);
                    let vi = l.vi();
                    if let Some(_) = targets.iter().find(|&&v| v == vi) {
                        let v = &mut self.vars[l.vi()];
                        v.num_occurs += 1;
                        v.occurs.push(ck.id_from(i));
                    }
                }
            }
        }
        let cnt = targets.len();
        let vol = self.vars.iter().map(|ref c| c.occurs.len()).sum::<usize>();
        let total = self.cp[1].clauses.len() + self.cp[2].clauses.len() - 2;
        println!("#elim, target:var|clause, {:>8}, {:>8}, clauses: {:>8}", cnt, vol, total);
    }
    /// 8. gatherTouchedClauses
    pub fn gather_touched_clauses(&mut self) -> () {
        if self.eliminator.n_touched == 0 {
            return;
        }
        let mut len = self.eliminator.subsumption_queue.len();
        for cid in &self.eliminator.subsumption_queue {
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            c.touched = true;
        }
        for kind in &[
            ClauseKind::Removable,
            ClauseKind::Binclause,
            ClauseKind::Permanent,
        ] {
            let clauses = &mut self.cp[*kind as usize].clauses;
            'next_clause: for i in 1..clauses.len() {
                let c = &mut clauses[i];
                if c.index == DEAD_CLAUSE {
                    continue 'next_clause;
                }
                if !c.touched {
                    for j in 1..c.len() {
                        let l = lindex!(c, j);
                        if self.vars[l.vi()].touched {
                            self.eliminator.subsumption_queue.push(kind.id_from(i));
                            c.touched = true;
                            len += 1;
                            if self.eliminator.subsume_clause_size < len {
                                break;
                            }
                            continue 'next_clause;
                        }
                    }
                }
            }
        }
        for cid in &self.eliminator.subsumption_queue {
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            c.touched = false;
        }
        for v in &mut self.vars {
            v.touched = false;
        }
        self.eliminator.n_touched = 0;
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
                self.eliminator
                    .subsumption_queue
                    .push(self.eliminator.bwdsub_tmp_clause.index);
            }
            let cid = self.eliminator.subsumption_queue[0];
            self.eliminator.subsumption_queue.remove(0);
            unsafe {
                let mut c = if cid == self.eliminator.bwdsub_tmp_clause.index {
                    &mut self.eliminator.bwdsub_tmp_clause as *mut Clause
                } else {
                    &mut self.cp[cid.to_kind()].clauses[cid.to_index()] as *mut Clause
                };
                // println!("poped {} from queue", *c);
                if (*c).sve_mark || (*c).index == DEAD_CLAUSE {
                    continue;
                }
                // println!("check with {} for best_v {}", *c, self.eliminator.best_v);
                debug_assert!(1 < (*c).len() || self.assigned((*c).lit[0]) == LTRUE);
                // unit clauses should have been propagated before this point.
                // Find best variable to scan:
                let mut best = 0;
                let mut tmp = 0;
                'next_var: for i in 0..(*c).len() {
                    let l = lindex!(*c, i);
                    let v = &self.vars[l.vi()];
                    // println!("select var {}, {}, {}", l.vi(), v.terminal, v.occurs.len());
                    if v.terminal && tmp < v.occurs.len() {
                        best = l.vi();
                        tmp = v.occurs.len();
                    }
                }
                // println!("select var {}", best);
                if best == 0 {
                    continue;
                }
                // Search all candidates:
                let cs = &mut self.vars[best].occurs as *mut Vec<ClauseId>;
                for di in &*cs {
                    let d = &self.cp[di.to_kind()].clauses[di.to_index()] as *const Clause;
                    if (*c).sve_mark || (*d).index == DEAD_CLAUSE {
                        continue;
                    }
                    if (!(*d).sve_mark || (*d).index != DEAD_CLAUSE) && *di != cid && self.eliminator.subsumption_lim == 0
                        || (*d).len() < self.eliminator.subsumption_lim
                    {
                        // println!("{} + {}", *c, *d);
                        match (*c).subsumes(&*d) {
                            Some(NULL_LIT) => {
                                // println!("    => {} subsumed completely by {}", (*d), (*c));
                                subsumed += 1;
                                self.remove_clause(*di);
                            }
                            Some(l) => {
                                // println!("     => subsumed {} from {}", l.int(), *d);
                                deleted_literals += 1;
                                if !self.strengthen_clause(*di, l.negate()) {
                                    return false;
                                }
                                // if l.vi() == best_v {
                                //     j -= 1;
                                // }
                            }
                            None => {}
                        }
                    }
                }
                self.eliminator.targets.clear();
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
        // FIXME WHY? Store the length of the clause last:
        vec.push(c.len() as u32);
    }
    /// 15. eliminateVar
    pub fn eliminate_var(&mut self, v: VarId) -> bool {
        if !self.vars[v].terminal {
            return true;
        }
        let mut pos: Vec<ClauseId> = Vec::new();
        let mut neg: Vec<ClauseId> = Vec::new();
        // Split the occurrences into positive and negative:
        for cid in &self.vars[v].occurs {
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
        unsafe {
            // Check wether the increase in number of clauses stays within the allowed ('grow').
            // Moreover, no clause must exceed the limit on the maximal clause size (if it is set).
            let clslen = pos.len() + neg.len();
            let mut cnt = 0;
            for i in 0..pos.len() {
                for j in 0..neg.len() {
                    let (res, clause_size) = self.check_to_merge(pos[i], neg[j], v);
                    if res {
                        cnt += 1;
                        if clslen + GROW < cnt
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
            // println!("- eliminate_var: {:>5} (+{:<4} -{:<4}).", v, pos.len(), neg.len());
            // setDecisionVar(v, false);
            self.eliminator.eliminated_vars += 1;
            {
                let tmp = &mut self.eliminator.elim_clauses as *mut Vec<Lit>;
                if neg.len() < pos.len() {
                    for cid in &neg {
                        self.make_eliminated_clause(&mut (*tmp), v, *cid);
                    }
                    self.make_eliminating_unit_clause(&mut (*tmp), v.lit(LTRUE));
                } else {
                    for cid in &pos {
                        self.make_eliminated_clause(&mut (*tmp), v, *cid);
                    }
                    self.make_eliminating_unit_clause(&mut (*tmp), v.lit(LFALSE));
                }
            }
            // Produce clauses in cross product via self.merge_vec:
            {
                // let vec = &self.eliminator.merge_vec as *const Vec<Lit>;
                for p in &pos {
                    for n in &neg {
                        if let Some(vec) = self.merge(*p, *n, v) {
                            if !self.add_cross(vec) {
                                return false;
                            }
                        }
                    }
                }
            }
            let cis = &self.vars[v].occurs as *const Vec<ClauseId>;
            for ci in &*cis {
                self.remove_clause(*ci);
            }
            self.vars[v].occurs.clear();
            // Free occurs list for this variable:
            // self.vars[v].occurs.clear();
            // FIXME I can't understand Glucose code!
            // Free watches lists for this variables, if possible:
            for ck in &[ClauseKind::Permanent, ClauseKind::Removable] {
                let cv = &self.cp[*ck as usize];
                if cv.watcher[v.lit(LTRUE) as usize] != NULL_CLAUSE {
                    // watches[v.lit(true)].clear();
                }
                if cv.watcher[v.lit(LFALSE) as usize] != NULL_CLAUSE {
                    // watches[v.lit(false)].clear();
                }
            }
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
            println!(" - fixed {}", l.int());
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
        self.eliminator.subsumption_queue.clear();
        self.build_occurence_list();
        for kind in &[
            ClauseKind::Removable,
            ClauseKind::Binclause,
            ClauseKind::Permanent,
        ] {
            let clauses = &mut self.cp[*kind as usize].clauses;
            'next_clause: for i in 1..clauses.len() {
                let c = &mut clauses[i];
                if c.len() < self.eliminator.subsume_clause_size {
                    self.eliminator.subsumption_queue.push(kind.id_from(i));
                }
            }
        }
        // println!("eliminate queue {:?}", self.eliminator.subsumption_queue);
        let mut tmp: Vec<(VarId, usize)> = self
            .vars
            .iter()
            .filter(|v| v.terminal)
            .map(|v| (v.index, v.occurs.len()))
            .collect::<Vec<_>>();
        tmp.sort_by_key(|t| (t.1 as isize).neg());
        self.eliminator.heap_tmp = tmp.iter().map(|v| v.0).collect::<Vec<_>>();
        // println!("eliminate heap {:?}", self.eliminator.heap_tmp);
        'perform: while 0 < self.eliminator.n_touched
            || self.eliminator.bwdsub_assigns < self.trail.len()
            || 0 < self.eliminator.heap_tmp.len()
        {
            let mut best_v = 1;
            for i in 2..self.vars.len() {
                if self.vars[best_v].occurs.len() < self.vars[i].occurs.len() {
                    best_v = i;
                }
            }
            self.vars[best_v].occurs.clear();
            self.eliminator.best_v = best_v;
            self.gather_touched_clauses();
            {
                if SUBSUMPTION_QUEUE_MAX < self.eliminator.subsumption_queue.len() {
                    println!("Too many clauses to eliminate");
                    if 0 < self.eliminator.subsume_clause_size {
                        self.eliminator.subsume_clause_size -= 1;
                    }
                    self.eliminator.subsumption_queue.clear();
                    return;
                }
            }
            // println!(" - queue {:?}", self.eliminator.subsumption_queue);
            if (0 < self.eliminator.subsumption_queue.len()
                || self.eliminator.bwdsub_assigns < self.trail.len())
                && !self.backward_subsumption_check()
            {
                self.ok = false;
                break 'perform; // goto cleaup
            }
            // abort after too long computation
            // if false { break 'perform; }
            // println!(" - heap: {:?}", self.eliminator.heap_tmp.len());
            while let Some(elim) = self.eliminator.heap_tmp.pop() {
                // let elim: VarId = self.vars.get_root(&mut self.eliminator.heap); // removeMin();
                // if asynch_interrupt { break }
                if self.vars[elim].eliminated || self.vars[elim].assign != BOTTOM {
                    continue;
                }
                if self.eliminator.use_elim
                    && self.vars[elim].assign == BOTTOM
                    && !self.vars[elim].frozen
                    && !self.eliminate_var(elim)
                {
                    self.ok = false;
                    break 'perform;
                }
                // println!("len {}", self.eliminator.heap_tmp.len());
            }
        }
    }
}

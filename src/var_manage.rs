#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]
use clause::Clause;
use clause::ClauseFlag;
use clause::ClauseIdIndexEncoding;
use clause::ClauseKind;
use clause::CLAUSE_KINDS;
use clause::DEAD_CLAUSE;
use solver::CDCL;
use solver::{Solver, Stat};
use types::*;
use var::Eliminator;
use var::Satisfiability;
use var::VarOrdering;

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;
const SUBSUMPITON_GROW_LIMIT: usize = 0;
const SUBSUMPTION_VAR_QUEUE_MAX: usize = 10_000;
const SUBSUMPTION_CLAUSE_QUEUE_MAX: usize = 10_000;
const SUBSUMPTION_COMBINATION_MAX: usize = 10_000_000;

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
        let d = self.stats[Stat::Conflict as usize] as f64;
        let a = (self.vars[vi].activity + d) / 2.0;
        self.vars[vi].activity = a;
        if VAR_ACTIVITY_THRESHOLD < a {
            // self.rescale_var_activity();
            for i in 1..self.vars.len() {
                self.vars[i].activity /= VAR_ACTIVITY_THRESHOLD;
            }
            self.var_inc /= VAR_ACTIVITY_THRESHOLD;
        }
        self.var_order.update(&self.vars, vi);
    }
    fn decay_var_activity(&mut self) -> () {
        self.var_inc /= VAR_ACTIVITY_THRESHOLD;
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
        let cid = self.attach_clause(Clause::new(ClauseKind::Permanent, false, vec.len(), &vec));
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
            if !v.eliminated && v.terminal {
                v.occurs.push(cid);
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
            let vi = lindex!(c, i).vi();
            if vars[vi].terminal {
                vars[vi].occurs.retain(|&ci| ci != cid);
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
                self.vars[l.vi()].occurs.retain(|&ci| ci != cid);
                if self.vars[l.vi()].terminal {
                    self.eliminator.enqueue_var(l.vi());
                }
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
            if !self.enqueue(c0, NULL_CLAUSE) {
                panic!("GGGGGGGGGGGGGGGGGGGGGGGGGG");
            }
            self.propagate() == NULL_CLAUSE
        // self.enqueue(c0, NULL_CLAUSE) == true && self.propagate() == NULL_CLAUSE
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
                    let lit_j = lindex!(p, j);
                    if lit_j.vi() == l.vi() {
                        if lit_j.negate() == l {
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
                    let lit_j = lindex!(p, j);
                    if lit_j.vi() == l.vi() {
                        if lit_j.negate() == l {
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
            self.vars[i].terminal = false;
            self.vars[i].max_clause_size = 0;
            self.vars[i].num_occurs = 0;
            self.vars[i].occurs.clear();
        }
        let mut total = 0;
        let mut cnt = 0;
        let nv = self.vars.len();
        for vi in 1..nv {
            let v = &mut self.vars[vi]; //  [nv - vi];
            if v.eliminated || v.assign != BOTTOM {
                continue;
            }
            v.terminal = true;
            total += v.num_occurs;
            cnt += 1;
            if self.eliminator.enqueue_var(v.index) {
                v.terminal = false;
            }
            if SUBSUMPTION_COMBINATION_MAX < total {
                break;
            }
        }
        // println!("targets {:?}", &targets[..5]);
        for ck in &CLAUSE_KINDS[0..3] {
            let clauses = &self.cp[*ck as usize].clauses;
            for (i, c) in clauses.iter().enumerate().skip(1) {
                if c.index == DEAD_CLAUSE {
                    continue;
                }
                for j in 0..c.len() {
                    let l = lindex!(c, j);
                    let v = &mut self.vars[l.vi()];
                    if v.terminal {
                        v.num_occurs += 1;
                        v.occurs.push(ck.id_from(i));
                    }
                }
            }
        }
        println!(
            "#elim, target:kernel size|var|clause, {:>4}, {:>8}, {:>8}",
            self.eliminator.subsume_clause_size, cnt, total,
        );
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
            c.set_flag(ClauseFlag::Touched, true);
        }
        for mut v in &mut self.vars[1..] {
            if v.touched && v.terminal {
                // println!("gtc var: {}", v.index);
                for cid in &v.occurs {
                    let mut c = mref!(self.cp, cid);
                    if !c.get_flag(ClauseFlag::Touched) {
                        self.eliminator.enqueue_clause(*cid);
                        c.set_flag(ClauseFlag::Touched, true);
                    }
                }
                v.touched = false;
            }
        }
        // println!("gather_touched_classes: clause_queue {}", self.eliminator.clause_queue.len());
        for cid in &self.eliminator.clause_queue {
            let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()];
            c.set_flag(ClauseFlag::Touched, false);
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
        while !self.eliminator.clause_queue.is_empty()
            || self.eliminator.bwdsub_assigns < self.trail.len()
        {
            // Empty subsumption queue and return immediately on user-interrupt:
            // if computed-too-long { break; }
            // Check top-level assigments by creating a dummy clause and placing it in the queue:
            if self.eliminator.clause_queue.is_empty()
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
                if (*c).get_flag(ClauseFlag::SveMark) || (*c).index == DEAD_CLAUSE {
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
                    if (!(*d).get_flag(ClauseFlag::SveMark) || (*d).index != DEAD_CLAUSE)
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
        // Store the length of the clause last:
        vec.push(c.len() as u32);
    }
    /// 15. eliminateVar
    pub fn eliminate_var(&mut self, v: VarId) -> bool {
        debug_assert!(!self.vars[v].eliminated);
        if !self.vars[v].terminal {
            return true;
        }
        let mut pos: Vec<ClauseId> = Vec::new();
        let mut neg: Vec<ClauseId> = Vec::new();
        // Split the occurrences into positive and negative:
        for cid in &self.vars[v].occurs {
            let c = &self.cp[cid.to_kind()].clauses[cid.to_index()];
            if c.index == DEAD_CLAUSE {
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
                        if clslen + SUBSUMPITON_GROW_LIMIT < cnt
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
        self.eliminator.clause_queue.clear();
        self.eliminator.var_queue.clear();
        self.build_occurence_list();
        // for i in 1..4 { println!("eliminate report: v{} => {},{}", i, self.vars[i].num_occurs, self.vars[i].occurs.len()); }
        'perform: while 0 < self.eliminator.n_touched
            || self.eliminator.bwdsub_assigns < self.trail.len()
            || !self.eliminator.var_queue.is_empty()
        {
            self.gather_touched_clauses();
            if (!self.eliminator.clause_queue.is_empty()
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
                    || !self.vars[elim].terminal
                    || self.vars[elim].frozen
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

#![allow(unused_mut)]
#![allow(unused_variables)]
use clause::{ClauseBody, ClauseHead, ClauseFlag, ClauseIdIndexEncoding, ClauseKind, ClauseManagement, ClausePartition, CLAUSE_KINDS, GC};
use solver::{CDCL, Solver};
use std::usize::MAX;
use std::fmt;
use types::*;

pub trait ClauseElimination {
    fn eliminator_enqueue(&mut self, cid: ClauseId) -> ();
}

const DEAD_CLAUSE: usize = MAX;
const BWDSUB_DUMMY_CLAUSE: ClauseId = DEAD_CLAUSE - 1;
const SUBSUMPTION_SIZE: usize = 20;
const SUBSUMPITON_GROW_LIMIT: usize = 0;
const SUBSUMPTION_VAR_QUEUE_MAX: usize = 10_000;
const SUBSUMPTION_CLAUSE_QUEUE_MAX: usize = 10_000;
const SUBSUMPTION_COMBINATION_MAX: usize = 10_000_000;

/// Literal eliminator
#[derive(Debug)]
pub struct Eliminator {
    pub merges: usize,
    /// renamed elimHeap. FIXME: can we use VarIdHeap here?
    pub var_queue: Vec<VarId>,
    pub n_touched: usize,
    pub asymm_lits: usize,
    pub clause_queue: Vec<ClauseId>,
    pub bwdsub_assigns: usize,
    //    pub bwdsub_tmp_unit: ClauseId,
    pub bwdsub_lit: Lit,
    pub remove_satisfied: bool,
    // working place
    pub merge_vec: Vec<Lit>,
    pub elim_clauses: Vec<Lit>,
    /// Variables are not eliminated if it produces a resolvent with a length above this limit.
    /// 0 means no limit.
    pub clause_lim: usize,
    pub eliminated_vars: usize,
    pub add_tmp: Vec<Lit>,
    pub use_elim: bool,
    pub turn_off_elim: bool,
    pub use_simplification: bool,
    pub subsumption_lim: usize,
    pub targets: Vec<ClauseId>,
    pub subsume_clause_size: usize,
    pub last_invocatiton: usize,
    pub binclause_queue: Vec<ClauseId>,
}

impl Eliminator {
    pub fn new(use_elim: bool, nv: usize) -> Eliminator {
        // let heap = VarIdHeap::new(VarOrder::ByOccurence, nv, 0);
        Eliminator {
            merges: 0,
            var_queue: Vec::new(),
            n_touched: 0,
            asymm_lits: 0,
            clause_queue: Vec::new(),
            bwdsub_assigns: 0,
            //            bwdsub_tmp_unit: 0,
            bwdsub_lit: NULL_LIT,
            remove_satisfied: false,
            merge_vec: vec![0; nv + 1],
            elim_clauses: Vec::new(),
            clause_lim: 20,
            eliminated_vars: 0,
            add_tmp: Vec::new(),
            use_elim,
            turn_off_elim: false,
            use_simplification: true,
            subsumption_lim: 0,
            targets: Vec::new(),
            subsume_clause_size: SUBSUMPTION_SIZE,
            last_invocatiton: 0,
            binclause_queue: Vec::new(),
        }
    }
}

impl fmt::Display for Eliminator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            " - n_touched {}\n - clause_queue {:?}\n - heap {:?}",
            self.n_touched,
            self.clause_queue,
            self.var_queue,
        )
    }
}

impl ClauseElimination for Solver {
    fn eliminator_enqueue(&mut self, cid: ClauseId) -> () {
        for l in &clause_head!(self.cp, cid).lit {
            let mut v = &mut self.vars[l.vi()];
            v.touched = true;
            self.eliminator.n_touched += 1;
            if !v.eliminated && v.terminal {
                v.occurs.push(cid);
            }
        }
        let cb = clause_body_mut!(self.cp, cid);
        for l in &cb.lits {
            let mut v = &mut self.vars[l.vi()];
            v.touched = true;
            self.eliminator.n_touched += 1;
            if !v.eliminated && v.terminal {
                v.occurs.push(cid);
            }
        }
        if !cb.get_flag(ClauseFlag::Queued) {
            self.subsume_queue.push(cid);
            cb.set_flag(ClauseFlag::Queued, true);
        }
    }
}

impl Solver {
    /// 3. addClause
    /// - calls `enqueue_clause`
    pub fn add_cross(&mut self, vec: &[Lit]) -> bool {
        if vec.len() == 1 {
            self.enqueue(vec[0], NULL_CLAUSE);
            return true;
        }
        let cid = self.add_clause(&mut vec.to_vec(), 0);
        // println!("add cross clause {}:{}", cid.to_kind(), cid.to_index());
        let ch = clause_head!(self.cp, cid);
        let cb = clause_body!(self.cp, cid);
        self.eliminator.enqueue_clause(cid);
        for i in 0..cb.lits.len() + 2 {
            let l = lindex!(ch, cb, i);
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
        {
            clause_body_mut!(self.cp, cid).set_flag(ClauseFlag::Dead, true);
            let w0;
            let w1;
            {
                let ch = clause_head!(self.cp, cid);
                w0 = ch.lit[0].negate();
                w1 = ch.lit[1].negate();
            }
            self.cp[cid.to_kind()].touched[w0 as usize] = true;
            self.cp[cid.to_kind()].touched[w1 as usize] = true;
        }
        let Solver {
            ref mut cp,
            ref mut vars,
            ref mut eliminator,
            ..
        } = self;
        {
            let ch = clause_head!(cp, cid);
            let cb = clause_body!(cp, cid);
            for i in 0..cb.lits.len() + 2 {
                let vi = lindex!(ch, cb, i).vi();
                if vars[vi].terminal {
                    vars[vi].occurs.retain(|&ci| ci != cid);
                    eliminator.enqueue_var(vi);
                }
            }
        }
        // println!("     - remove_clause made {} dead", cid.to_index());
    }
    /// 5. strengthenClause
    /// - calls `enqueue_clause`
    /// - calls `enqueue_var`
    pub fn strengthen_clause(&mut self, cid: ClauseId, l: Lit) -> bool {
        // println!("STRENGTHEN_CLAUSE {}:{}", cid.to_kind(), cid.to_index());
        let c0;
        {
            debug_assert_ne!(cid, NULL_CLAUSE);
            if clause_body!(self.cp, cid).lits.is_empty() {
                // println!("{} is a binclause", cid);
                let res = self.strengthen(cid, l);
                debug_assert!(res);
                c0 = clause_head!(self.cp, cid).lit[0];
            } else {
                let res = self.strengthen(cid, l);
                debug_assert!(!res);
                self.vars[l.vi()].occurs.retain(|&ci| ci != cid);
                if self.vars[l.vi()].terminal {
                    self.eliminator.enqueue_var(l.vi());
                }
                c0 = NULL_LIT;
            }
        }
        if c0 != NULL_LIT {
            // println!("{} is removed.", cid);
            self.remove_clause(cid);
            // before the following propagate, we need to clean garbages.
            self.cp[cid.to_kind()].garbage_collect();
            // self.cp[ClauseKind::Removable as usize].garbage_collect();
            // self.cp[ClauseKind::Permanent as usize].garbage_collect();
            // self.cp[ClauseKind::Binclause as usize].garbage_collect();
            // println!("STRENGTHEN_CLAUSE ENQUEUE {}", c0);
            if !self.enqueue(c0, NULL_CLAUSE) {
                self.ok = false;
                return false;
            }
            true
        // self.enqueue(c0, NULL_CLAUSE) == true && self.propagate() == NULL_CLAUSE
        } else {
            self.eliminator.enqueue_clause(cid);
            true
        }
    }
    /// 6. merge(1)
    /// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
    pub fn merge(&mut self, cp: ClauseId, cq: ClauseId, v: VarId) -> Option<Vec<Lit>> {
        let mut vec: Vec<Lit> = Vec::new();
        self.eliminator.merges += 1;
        self.eliminator.merge_vec.clear();
        let pqh = clause_head!(self.cp, cp);
        let pqb = clause_body!(self.cp, cp);
        let qph = clause_head!(self.cp, cq);
        let qpb = clause_body!(self.cp, cq);
        let ps_smallest = pqb.lits.len() < qpb.lits.len();
        let (ph, pb, qh, qb) = if ps_smallest { (pqh, pqb, qph, qpb) } else { (qph, qpb, pqh, pqb) };
        'next_literal: for i in 0..qb.lits.len() + 2 {
            let l = lindex!(qh, qb, i);
            if l.vi() != v {
                for j in 0..pb.lits.len() {
                    let lit_j = lindex!(ph, pb, j);
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
        for i in 0..pb.lits.len() {
            let l = lindex!(ph, pb, i);
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
        let pqh = clause_head!(self.cp, cp);
        let pqb = clause_body!(self.cp, cp);
        let qph = clause_head!(self.cp, cq);
        let qpb = clause_body!(self.cp, cq);
        let ps_smallest = pqb.lits.len() < qpb.lits.len();
        let (ph, pb, qh, qb) = if ps_smallest { (pqh, pqb, qph, qpb) } else { (qph, qpb, pqh, pqb) };
        let mut size = pb.lits.len() + 1;
        'next_literal: for i in 0..qb.lits.len() + 2 {
            let l = lindex!(qh, qb, i);
            if l.vi() != v {
                for j in 0..pb.lits.len() {
                    let lit_j = lindex!(ph, pb, j);
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
            let head = &self.cp[*ck as usize].head;
            let body = &self.cp[*ck as usize].body;
            for i in 1..head.len() {
                let ch = &head[i];
                let cb = &body[i];
                if cb.get_flag(ClauseFlag::Dead) {
                    continue;
                }
                for j in 0..cb.lits.len() + 2 {
                    let l = lindex!(ch, cb, j);
                    let v = &mut self.vars[l.vi()];
                    if v.terminal {
                        v.num_occurs += 1;
                        v.occurs.push(ck.id_from(i));
                    }
                }
            }
        }
        // println!(
        //     "#elim, target:kernel size|var|clause, {:>4}, {:>8}, {:>8}",
        //     self.eliminator.subsume_clause_size, cnt, total,
        // );
    }
    /// 8. gatherTouchedClauses
    /// - calls `enqueue_clause`
    pub fn gather_touched_clauses(&mut self) -> () {
        if self.eliminator.n_touched == 0 {
            return;
        }
        let mut len = self.eliminator.clause_queue.len();
        for cid in &self.eliminator.clause_queue {
            clause_body_mut!(self.cp, cid).set_flag(ClauseFlag::Touched, true);
        }
        for mut v in &mut self.vars[1..] {
            if v.touched && v.terminal {
                // println!("gtc var: {}", v.index);
                for cid in &v.occurs {
                    let mut cb = clause_body_mut!(self.cp, cid);
                    if !cb.get_flag(ClauseFlag::Touched) {
                        self.eliminator.enqueue_clause(*cid);
                        cb.set_flag(ClauseFlag::Touched, true);
                    }
                }
                v.touched = false;
            }
        }
        // println!("gather_touched_classes: clause_queue {}", self.eliminator.clause_queue.len());
        for cid in &self.eliminator.clause_queue {
            clause_body_mut!(self.cp, cid).set_flag(ClauseFlag::Touched, false);
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
                self.eliminator.bwdsub_lit = self.trail[self.eliminator.bwdsub_assigns];
                // self.eliminator.bwdsub_tmp_clause.lit[0] = l;
                self.eliminator.bwdsub_assigns += 1;
                self.eliminator.enqueue_clause(BWDSUB_DUMMY_CLAUSE);
            }
            let cid = self.eliminator.clause_queue[0];
            self.eliminator.clause_queue.remove(0);
            unsafe {
                let mut best = 0;
                if cid == BWDSUB_DUMMY_CLAUSE {
                    best = self.eliminator.bwdsub_lit.vi() as usize;
                    let cs = &mut self.vars[best].occurs as *mut Vec<ClauseId>;
                    for di in &*cs {
                        let db = clause_body!(self.cp, di) as *const ClauseBody;
                        match self.subsume(cid, *di) {
                            Some(NULL_LIT) => {
                                subsumed += 1;
                                self.remove_clause(*di);
                            }
                            Some(l) => {
                                deleted_literals += 1;
                                if !self.strengthen_clause(*di, l.negate()) {
                                    return false;
                                }
                            }
                            None => {}
                        }
                    }
                    self.eliminator.targets.clear();
                } else {
                    let mut tmp = 0;
                    let ch = clause_head_mut!(self.cp, cid) as *mut ClauseHead;
                    let cb = clause_body_mut!(self.cp, cid) as *mut ClauseBody;
                    if (*cb).get_flag(ClauseFlag::SveMark) || (*cb).get_flag(ClauseFlag::Dead) {
                        continue;
                    }
                    for i in 0..(*cb).lits.len() {
                        let l = lindex!(*ch, *cb, i);
                        {
                            let v = &self.vars[l.vi()];
                            if v.terminal && tmp < v.occurs.len() {
                                best = l.vi();
                                tmp = v.occurs.len();
                            }
                        }
                        if best == 0 {
                            continue;
                        }
                        // Search all candidates:
                        let cs = &mut self.vars[best].occurs as *mut Vec<ClauseId>;
                        for di in &*cs {
                            let db = clause_body!(self.cp, di) as *const ClauseBody;
                            if (!(*db).get_flag(ClauseFlag::SveMark) || !(*db).get_flag(ClauseFlag::Dead))
                                && *di != cid
                                && (*cb).lits.len() + 2 <= self.eliminator.subsume_clause_size
                                && (*db).lits.len() + 2 <= self.eliminator.subsume_clause_size
                                && (self.eliminator.subsumption_lim == 0
                                    || (*cb).lits.len() + (*db).lits.len() + 4 <= self.eliminator.subsumption_lim)
                            // && (self.eliminator.subsumption_lim == 0 || (*d).len() < self.eliminator.subsumption_lim)
                            {
                                // println!("{} + {}", cid, *di);
                                match self.subsume(cid, *di) {
                                    Some(NULL_LIT) => {
                                        // println!("BackSubsC    => {} subsumed completely by {}", *di, cid);
                                        subsumed += 1;
                                        self.remove_clause(*di);
                                    }
                                    Some(l) => {
                                        // println!("BackSubsC    => subsumed {} from {} and {}", l.int(), cid, *di);
                                        deleted_literals += 1;
                                        if !self.strengthen_clause(*di, l.negate()) {
                                            return false;
                                        }
                                        self.propagate();
                                    }
                                    None => {}
                                }
                            }
                        }
                    self.eliminator.targets.clear();
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
        let ch = clause_head!(self.cp, cid);
        let cb = clause_body!(self.cp, cid);
        for i in 0..cb.lits.len() + 2 {
            let l = lindex!(ch, cb, i);
            vec.push(l as u32);
            if l.vi() == vi {
                let index = vec.len() - 1;
                // swap the first literal with the 'v'. So that the literal containing 'v' will occur first in the clause.
                vec.swap(index, first);
            }
        }
        // Store the length of the clause last:
        vec.push((cb.lits.len() + 2) as Lit);
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
            let ch = clause_head!(self.cp, cid);
            let cb = clause_body!(self.cp, cid);
            if cb.get_flag(ClauseFlag::Dead) {
                continue;
            }
            for i in 0..cb.lits.len() + 2 {
                let l = lindex!(ch, cb, i);
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
            for lit_pos in &pos {
                for lit_neg in &neg {
                    let (res, clause_size) = self.check_to_merge(*lit_pos, *lit_neg, v);
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
                            if !self.add_cross(&vec) {
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
        // println!("clause_queue {:?}", self.eliminator.clause_queue);
        // println!("var_queue {:?}", self.eliminator.var_queue);
        // println!("n_touched {}", self.eliminator.n_touched);
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
                break 'perform;
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
                // FIXME!
                // if !self.eliminate_var(elim) {
                //     self.ok = false;
                //     break 'perform;
                // }
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

impl Solver {
    fn subsume(&self, cid: ClauseId, other: ClauseId) -> Option<Lit> {
        let mut ret: Lit = NULL_LIT;
        let ch = clause_head!(self.cp, cid);
        let cb = clause_body!(self.cp, cid);
        let oh = clause_head!(self.cp, other);
        let ob = clause_body!(self.cp, other);
        'next: for i in 0..cb.lits.len() + 2 {
            let l = lindex!(ch, cb, i);
            for j in 0..ob.lits.len() + 2 {
                let lo = lindex!(oh, ob, j);
                if l == lo {
                    continue 'next;
                } else if ret == NULL_LIT && l == lo.negate() {
                    ret = l;
                    continue 'next;
                }
            }
            return None;
        }
        Some(ret)
    }

    /// remove Lit `p` from Clause *self*. This is an O(n) function!
    /// returns true if the clause became a unit clause.
    pub fn strengthen(&mut self, cid: ClauseId, p: Lit) -> bool {
        let cix = cid.to_index();
        let mut cj;
        let mut next;
        let new_watcher;
        let update;
        let ClausePartition {
            ref mut head,
            ref mut body,
            ref mut watcher,
            ..
        } = self.cp[cid.to_kind()];
        unsafe {
            let ch = &mut head[cid.to_index()] as *mut ClauseHead;
            let cb = &mut body[cid.to_index()] as *mut ClauseBody;
            if (*cb).get_flag(ClauseFlag::Dead) {
                return false;
            }
            if (*cb).lits.is_empty() {
                if (*ch).lit[0] == p {
                    (*ch).lit.swap(0, 1);
                    (*ch).next_watcher.swap(0, 1);
                }
                return true;
            }
            if (*ch).lit[0] != p && (*ch).lit[1] != p {
                (*cb).lits.retain(|&x| x != p);
                return false;
            }
            debug_assert!((*ch).lit[0] == p || (*ch).lit[1] == p);
            new_watcher = (*cb).lits.pop().unwrap();
            update = (*ch).lit[0] != p;
            debug_assert!((*ch).lit[update as usize] == p);
            next = (*ch).next_watcher[update as usize];
            (*ch).lit[update as usize] = new_watcher;
            (*ch).next_watcher[update as usize] = watcher[new_watcher.negate() as usize];
            watcher[new_watcher.negate() as usize] = cix;
            cj = &mut watcher[p.negate() as usize];
            while *cj != NULL_CLAUSE {
                if *cj == cix {
                    *cj = next;
                    break;
                }
                let ch = &mut head[*cj] as *mut ClauseHead;
                debug_assert!((*ch).lit[0] == p || (*ch).lit[1] == p);
                cj = &mut (*ch).next_watcher[((*ch).lit[0] != p) as usize];
            }
        }
        false
    }
    pub fn eliminate_binclauses(&mut self) -> () {
        if !self.eliminator.binclause_queue.is_empty() {
            self.build_binary_occurrence();
            self.binary_subsumption_check();
        }
    }
    /// remove all vars which have a single positive or negative occurence.
    pub fn build_binary_occurrence(&mut self) -> () {
        for v in &mut self.vars[1..] {
            v.bin_pos_occurs.clear();
            v.bin_neg_occurs.clear();
        }
        for i in 1..self.cp[ClauseKind::Binclause as usize].head.len() {
            let ch = &self.cp[ClauseKind::Binclause as usize].head[i];
            let cb = &self.cp[ClauseKind::Binclause as usize].body[i];
            let cid = ClauseKind::Binclause.id_from(i);
            if cb.get_flag(ClauseFlag::Dead) {
                continue;
            }
            for l in &ch.lit {
                let v = &mut self.vars[l.vi()];
                if l.positive() {
                    v.bin_pos_occurs.push(cid);
                } else {
                    v.bin_neg_occurs.push(cid);
                }
            }
            debug_assert_eq!(cb.lits.len(), 0);
        }
    }
    pub fn binary_subsumption_check(&mut self) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        unsafe {
            while let Some(cid) = self.eliminator.binclause_queue.pop() {
                debug_assert_eq!(cid.to_kind(), ClauseKind::Binclause as usize);
                let ch = clause_head!(self.cp, cid) as *const ClauseHead;
                let cb = clause_body!(self.cp, cid) as *const ClauseBody;
                if (*cb).get_flag(ClauseFlag::SveMark) || (*cb).get_flag(ClauseFlag::Dead) {
                    continue;
                }
                for l in &(*ch).lit {
                    if self.vars[l.vi()].eliminated {
                        continue;
                    }
                    let targets = if l.positive() {
                        &mut self.vars[l.vi()].bin_neg_occurs as *mut Vec<ClauseId>
                    } else {
                        &mut self.vars[l.vi()].bin_pos_occurs as *mut Vec<ClauseId>
                    };
                    for did in &*targets {
                        debug_assert_eq!(did.to_kind(), ClauseKind::Binclause as usize);
                        // println!("check with {} for best_v {}", *c, self.eliminator.best_v);
                        // Search all candidates:
                        let db = clause_body_mut!(self.cp, *did) as *mut ClauseBody;
                        if (*db).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
                        if !(*db).get_flag(ClauseFlag::Dead) && cid != *did {
                            // println!("{} + {}", *c, *d);
                            match self.subsume(cid, *did) {
                                Some(NULL_LIT) => {
                                    // println!("    => {} subsumed completely by {}", *did, cid);
                                    self.remove_clause(*did);
                                }
                                Some(l) => {
                                    // println!("    => subsumed {} from {} and {}", l.int(), cid, *did);
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
        self.propagate() == NULL_CLAUSE
    }
}

#![allow(unused_mut)]
#![allow(unused_variables)]
use clause::{ClauseBody, ClauseHead, ClauseFlag, ClauseIdIndexEncoding, ClauseKind, ClauseManagement, ClausePartition, GC};
use solver::{CDCL, Solver};
use std::fmt;
use types::*;
use var::Var;

// for Solver
pub trait ClauseElimination {
    fn eliminator_register_clause(&mut self, cid: ClauseId, rank: usize) -> ();
    fn eliminator_enqueue_clause(&mut self, cid: ClauseId) -> ();
    fn eliminator_enqueue_var(&mut self, vi: VarId) -> ();
}

// for Eliminator
pub trait EliminatorIF {
    fn new(use_elim: bool, nv: usize) -> Eliminator;
    fn enqueue_var(&mut self, v: &mut Var) -> ();
    fn clause_queue_len(&self) -> usize;
    fn var_queue_len(&self) -> usize;
}

/// Literal eliminator
#[derive(Debug)]
pub struct Eliminator {
    pub eliminated_vars: usize,
    pub use_elim: bool,
    pub use_simplification: bool,
    pub last_invocatiton: usize,
    n_touched: usize,
    merges: usize,
    clause_queue: Vec<ClauseId>,
    var_queue: Vec<VarId>,
    bwdsub_assigns: usize,
    // working place
    elim_clauses: Vec<Lit>,
    /// Variables are not eliminated if it produces a resolvent with a length above this limit.
    /// 0 means no limit.
    clause_lim: usize,
    subsumption_lim: usize,
    subsume_clause_size: usize,
    clause_queue_threshold: usize,
    var_queue_threshold: usize,
}

const SUBSUMPTION_SIZE: usize = 30;
const SUBSUMPITON_GROW_LIMIT: usize = 0;
const BACKWORD_SUBSUMPTION_THRESHOLD: usize = 10_000;
const CLAUSE_QUEUE_THRESHOD: usize = 1_000;
const VAR_QUEUE_THRESHOLD: usize = 3_200_000;


trait LiteralClause {
    fn as_uniclause(self) -> ClauseId;
}

impl LiteralClause for Lit {
    fn as_uniclause(self) -> ClauseId {
        ClauseKind::Uniclause.id_from(self as usize)
    }
}

impl EliminatorIF for Eliminator {
    fn new(use_elim: bool, nv: usize) -> Eliminator {
        Eliminator {
            merges: 0,
            var_queue: Vec::new(),
            n_touched: 0,
            clause_queue: Vec::new(),
            bwdsub_assigns: 0,
            elim_clauses: Vec::new(),
            clause_lim: 20,
            eliminated_vars: 0,
            use_elim,
            use_simplification: true,
            subsumption_lim: 0,
            subsume_clause_size: SUBSUMPTION_SIZE,
            last_invocatiton: 0,
            clause_queue_threshold: CLAUSE_QUEUE_THRESHOD,
            var_queue_threshold: VAR_QUEUE_THRESHOLD,
        }
    }
    fn enqueue_var(&mut self, v: &mut Var) -> () {
        if self.var_queue_threshold == 0 {
            return;
        }
        if !v.enqueued {
            self.var_queue.push(v.index);
            v.enqueued = true;
            self.var_queue_threshold -= 1;
        }
    }
    fn clause_queue_len(&self) -> usize {
        self.clause_queue.len()
    }
    fn var_queue_len(&self) -> usize {
        self.var_queue.len()
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
    fn eliminator_register_clause(&mut self, cid: ClauseId, rank: usize) -> () {
        {
        for l in &clause_head!(self.cp, cid).lit {
            let mut v = &mut self.vars[l.vi()];
            v.touched = true;
            if !v.eliminated {
                self.eliminator.n_touched += 1;
                if l.positive() {
                    v.pos_occurs.push(cid);
                } else {
                    v.neg_occurs.push(cid);
                }
            }
        }
        let cb = clause_body_mut!(self.cp, cid);
        for l in &cb.lits {
            let mut v = &mut self.vars[l.vi()];
            v.touched = true;
            self.eliminator.n_touched += 1;
            if !v.eliminated {
                if l.positive() {
                    v.pos_occurs.push(cid);
                } else {
                    v.neg_occurs.push(cid);
                }
            }
        }
        }
        self.eliminator_enqueue_clause(cid);
    }
    fn eliminator_enqueue_clause(&mut self, cid: ClauseId) -> () {
        if self.eliminator.clause_queue_threshold == 0 {
            return;
        }
        let cb = clause_body_mut!(self.cp, cid);
        let rank = cb.rank as f64;
        if !cb.get_flag(ClauseFlag::Enqueued) {
            let accept = if self.eliminator.clause_queue.len() <= 256 {
                rank
            } else {
                4.8 - ((self.eliminator.clause_queue.len() as f64).log(2.0) - 8.0)
            };
            if rank <= accept {
                self.eliminator.clause_queue.push(cid);
                // println!("increment {}", self.eliminator.clause_queue.len());
                cb.set_flag(ClauseFlag::Enqueued, true);
                self.eliminator.clause_queue_threshold -= 1;
            }
        }
    }
    fn eliminator_enqueue_var(&mut self, vi: VarId) -> () {
        self.eliminator.enqueue_var(&mut self.vars[vi])
    }
}

impl Solver {
    /// 4. removeClause
    /// called from strengthen_clause, backward_subsumption_check, eliminate_var, substitute
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
    }
    /// 5. strengthenClause
    /// returns false if inconsistent
    /// - calls `enqueue_clause`
    /// - calls `enqueue_var`
    pub fn strengthen_clause(&mut self, cid: ClauseId, l: Lit) -> bool {
        debug_assert!(!clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead));
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
                debug_assert!(!res); // if res is true, it means the clause is a unit clause now.
                self.eliminator_enqueue_var(l.vi());
                let v = &mut self.vars[l.vi()];
                debug_assert!(!v.eliminated);
                // let xx = (v.pos_occurs.len(), v.neg_occurs.len());
                if l.positive() {
                    v.pos_occurs.retain(|&ci| ci != cid);
                } else {
                    v.neg_occurs.retain(|&ci| ci != cid);
                }
                // let xy = (v.pos_occurs.len(), v.neg_occurs.len());
                // if (xy.0 + xy.1) + 1 < (xx.0 + xx.1) {
                //     panic!("strange {} {:?} {:?}", l, xx, xy);
                // }
                c0 = NULL_LIT;
            }
        }
        if c0 != NULL_LIT {
            // println!("{} is removed.", cid);
            self.remove_clause(cid);
            // before the following propagate, we need to clean garbages.
            self.cp[cid.to_kind()].garbage_collect(&mut self.vars, &mut self.eliminator);
            // println!("STRENGTHEN_CLAUSE ENQUEUE {}", c0);
            if !self.enqueue(c0, NULL_CLAUSE) {
                self.ok = false;
                return false;
            }
            true
        // self.enqueue(c0, NULL_CLAUSE) == true && self.propagate() == NULL_CLAUSE
        } else {
            self.eliminator_enqueue_clause(cid);
            true
        }
    }
    /// 6. merge(1)
    /// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
    pub fn merge(&mut self, cp: ClauseId, cq: ClauseId, v: VarId) -> Option<Vec<Lit>> {
        let mut vec: Vec<Lit> = Vec::new();
        self.eliminator.merges += 1;
        let pqh = clause_head!(self.cp, cp);
        let pqb = clause_body!(self.cp, cp);
        let qph = clause_head!(self.cp, cq);
        let qpb = clause_body!(self.cp, cq);
        let ps_smallest = pqb.lits.len() < qpb.lits.len();
        let (ph, pb, qh, qb) = if ps_smallest { (pqh, pqb, qph, qpb) } else { (qph, qpb, pqh, pqb) };
        // println!(" -  {:?}{:?} & {:?}{:?}", vec2int(&ph.lit),vec2int(&pb.lits),vec2int(&qh.lit),vec2int(&qb.lits));
        'next_literal: for i in 0..qb.lits.len() + 2 {
            let l = lindex!(qh, qb, i);
            if l.vi() != v {
                for j in 0..pb.lits.len() + 2 {
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
        for i in 0..pb.lits.len() + 2 {
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
    /// 8. gatherTouchedClauses
    /// - calls `enqueue_clause`
//     pub fn gather_touched_clauses(&mut self) -> () {
//         if self.eliminator.n_touched == 0 {
//             return;
//         }
//         let mut len = self.eliminator.clause_queue.len();
//         for cid in &self.eliminator.clause_queue {
//             clause_body_mut!(self.cp, cid).set_flag(ClauseFlag::Touched, true);
//         }
//         for mut v in &mut self.vars[1..] {
//             if v.touched {
//                 // println!("gtc var: {}", v.index);
//                 for cid in &v.pos_occurs {
//                     let mut cb = clause_body_mut!(self.cp, cid);
//                     if !cb.get_flag(ClauseFlag::Touched) {
//                         if !cb.get_flag(ClauseFlag::Enqueued) {
//                             self.eliminator.clause_queue.push(*cid);
//                             cb.set_flag(ClauseFlag::Enqueued, true);
//                         }
//                         cb.set_flag(ClauseFlag::Touched, true);
//                     }
//                 }
//                 for cid in &v.neg_occurs {
//                     let mut cb = clause_body_mut!(self.cp, cid);
//                     if !cb.get_flag(ClauseFlag::Touched) {
//                         if !cb.get_flag(ClauseFlag::Enqueued) {
//                             self.eliminator.clause_queue.push(*cid);
//                             cb.set_flag(ClauseFlag::Enqueued, true);
//                         }
//                         cb.set_flag(ClauseFlag::Touched, true);
//                     }
//                 }
//                 v.touched = false;
//             }
//         }
//         // println!("gather_touched_classes: clause_queue {}", self.eliminator.clause_queue.len());
//         for cid in &self.eliminator.clause_queue {
//             clause_body_mut!(self.cp, cid).set_flag(ClauseFlag::Touched, false);
//         }
//         for v in &mut self.vars {
//             v.touched = false;
//         }
//         self.eliminator.n_touched = 0;
//     }
    /// 10. backwardSubsumptionCheck
    /// returns false if solver is inconsistent
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
                let c = self.trail[self.eliminator.bwdsub_assigns].as_uniclause();
                self.eliminator.clause_queue.push(c);
                self.eliminator.bwdsub_assigns += 1;
            }
            let cid = self.eliminator.clause_queue[0];
            self.eliminator.clause_queue.remove(0);
            // println!("bsc remain clauses {} vars {}", self.eliminator.clause_queue.len(), self.eliminator.var_queue.len());
            unsafe {
                let mut best = 0;
                if cid.to_kind() == ClauseKind::Uniclause as usize {
                    best = (cid.to_index() as Lit).vi();
                    if self.vars[best].eliminated {
                        continue;
                    }
                    let cs = &mut self.vars[best].pos_occurs as *mut Vec<ClauseId>;
                    cnt += (*cs).len();
                    for di in &*cs {
                        let db = clause_body!(self.cp, di) as *const ClauseBody;
                        if (*db).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
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
                                self.eliminator_enqueue_var(l.vi());
                            }
                            None => {}
                        }
                    }
                    let cs = &mut self.vars[best].neg_occurs as *mut Vec<ClauseId>;
                    cnt += (*cs).len();
                    for di in &*cs {
                        let db = clause_body!(self.cp, di) as *const ClauseBody;
                        if (*db).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
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
                                self.eliminator_enqueue_var(l.vi());
                            }
                            None => {}
                        }
                    }
                } else {
                    let mut tmp = 0.0;
                    let ch = clause_head_mut!(self.cp, cid) as *mut ClauseHead;
                    let cb = clause_body_mut!(self.cp, cid) as *mut ClauseBody;
                    (*cb).set_flag(ClauseFlag::Enqueued, false);
                    if (*cb).get_flag(ClauseFlag::Dead) || BACKWORD_SUBSUMPTION_THRESHOLD < cnt {
                        continue;
                    }
                    for i in 0..(*cb).lits.len() {
                        let l = lindex!(*ch, *cb, i);
                        {
                            let v = &self.vars[l.vi()];
                            if v.eliminated || v.level == 0 {
                                continue;
                            }
                            let nsum = - v.activity;
                            // v.pos_occurs.len() + v.neg_occurs.len()
                            if tmp < nsum {
                                best = l.vi();
                                tmp = nsum;
                            }
                        }
                    }
                    if best == 0 {
                        continue;
                    }
                    // Search all candidates:
                    let cs = &mut self.vars[best].pos_occurs as *mut Vec<ClauseId>;
                    cnt += (*cs).len();
                    for di in &*cs {
                        let db = clause_body!(self.cp, di) as *const ClauseBody;
                        if !(*db).get_flag(ClauseFlag::Dead)
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
                                    self.eliminator_enqueue_var(l.vi());
                                    self.propagate();
                                }
                                None => {}
                            }
                        }
                    }
                    let cs = &mut self.vars[best].neg_occurs as *mut Vec<ClauseId>;
                    cnt += (*cs).len();
                    for di in &*cs {
                        let db = clause_body!(self.cp, di) as *const ClauseBody;
                        if !(*db).get_flag(ClauseFlag::Dead)
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
    /// returns false if solver is in inconsistent
    pub fn eliminate_var(&mut self, v: VarId) -> bool {
        if self.vars[v].assign != BOTTOM {
            return true;
        }
        assert!(!self.vars[v].eliminated);
        let pos = &self.vars[v].pos_occurs as *const Vec<ClauseId>;
        let neg = &self.vars[v].neg_occurs as *const Vec<ClauseId>;
        unsafe {
            // Check wether the increase in number of clauses stays within the allowed ('grow').
            // Moreover, no clause must exceed the limit on the maximal clause size (if it is set).
            let clslen = (*pos).len() + (*neg).len();
            let mut cnt = 0;
            for lit_pos in &*pos {
                if clause_body!(self.cp, lit_pos).get_flag(ClauseFlag::Dead) {
                    continue;
                }
                for lit_neg in &*neg {
                    if clause_body!(self.cp, lit_neg).get_flag(ClauseFlag::Dead) {
                        continue;
                }
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
            // eliminate the literal and build constraints on it.
            self.vars[v].eliminated = true;
            // println!("- eliminate: {:>5} (+{:<4} -{:<4})", v, (*pos).len(), (*neg).len() );
            // setDecisionVar(v, false);
            self.eliminator.eliminated_vars += 1;
            {
                let tmp = &mut self.eliminator.elim_clauses as *mut Vec<Lit>;
                if (*neg).len() < (*pos).len() {
                    for cid in &*neg {
                        if clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
                        self.make_eliminated_clause(&mut (*tmp), v, *cid);
                    }
                    self.make_eliminating_unit_clause(&mut (*tmp), v.lit(LTRUE));
                } else {
                    for cid in &*pos {
                        if clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
                        self.make_eliminated_clause(&mut (*tmp), v, *cid);
                    }
                    self.make_eliminating_unit_clause(&mut (*tmp), v.lit(LFALSE));
                }
            }
            // Produce clauses in cross product:
            {
                for p in &*pos {
                    if clause_body!(self.cp, p).get_flag(ClauseFlag::Dead) {
                        continue;
                    }
                    for n in &*neg {
                        if clause_body!(self.cp, n).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
                        if let Some(vec) = self.merge(*p, *n, v) {
                            self.add_clause(&mut vec.to_vec(), 0);
                        }
                    }
                }
            }
            for i in 0..self.vars[v].pos_occurs.len() {
                let cid = self.vars[v].pos_occurs[i];
                if clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead) {
                    continue;
                }
                self.remove_clause(cid);
            }
            for i in 0..self.vars[v].neg_occurs.len() {
                let cid = self.vars[v].neg_occurs[i];
                if clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead) {
                    continue;
                }
                self.remove_clause(cid);
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
        // println!("eliminate: clause_queue {}", self.eliminator.clause_queue.len());
        // println!("clause_queue {:?}", self.eliminator.clause_queue);
        // println!("var_queue {:?}", self.eliminator.var_queue);
        // println!("n_touched {}", self.eliminator.n_touched);
        // self.build_occurence_list();
        // for i in 1..4 { println!("eliminate report: v{} => {},{}", i, self.vars[i].num_occurs, self.vars[i].occurs.len()); }
        'perform: while self.eliminator.bwdsub_assigns < self.trail.len() || !self.eliminator.var_queue.is_empty()
        {
            // self.gather_touched_clauses();
            if (!self.eliminator.clause_queue.is_empty()
                || self.eliminator.bwdsub_assigns < self.trail.len())
                && !self.backward_subsumption_check()
            {
                self.ok = false;
                break 'perform;
            }
            while !self.eliminator.var_queue.is_empty() {
                let elim = self.eliminator.var_queue.remove(0);
                self.vars[elim].enqueued = false;
                if self.vars[elim].eliminated
                    || self.vars[elim].assign != BOTTOM
                    || self.vars[elim].frozen
                {
                    continue;
                }
                // FIXME!
                if !self.eliminate_var(elim) {
                    self.ok = false;
                    break 'perform;
                }
            }
        }
        self.eliminator.clause_queue_threshold = CLAUSE_QUEUE_THRESHOD;
        self.eliminator.var_queue_threshold = VAR_QUEUE_THRESHOLD;
    }
}

impl Solver {
   /// returns a literal if these clauses can be merged by the literal.
    fn subsume(&self, cid: ClauseId, other: ClauseId) -> Option<Lit> {
        if cid.to_kind() == ClauseKind::Uniclause as usize {
            let oh = clause_head!(self.cp, other);
            let ob = clause_body!(self.cp, other);
            let l = cid.to_index() as Lit;
            for j in 0..ob.lits.len() + 2 {
                let lo = lindex!(oh, ob, j);
                if l == lo.negate() {
                    return Some(l);
                }
            }
            return None;
        }
        // println!("subsume {} = {}:{}", cid, cid.to_kind(), cid.to_index());
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
        debug_assert!(!clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead));
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
}

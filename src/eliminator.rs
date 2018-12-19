#![allow(unreachable_code)]
#![allow(unused_mut)]
#![allow(unused_variables)]
use crate::clause::{
    cid2fmt, ClauseFlag, ClauseHead, ClauseIdIndexEncoding, ClauseIndex, ClauseKind,
    ClauseManagement, ClausePartition,
};
use crate::solver::{Solver, CDCL};
use crate::types::*;
use crate::var::{Satisfiability, Var};
#[test]
use std::fmt;

/// For Solver
pub trait ClauseElimination {
    fn check_eliminator(&self) -> bool;
}

/// For Eliminator
pub trait EliminatorIF {
    fn new(use_elim: bool, nv: usize) -> Eliminator;
    fn enqueue_clause(&mut self, cid: ClauseId, ch: &mut ClauseHead) -> ();
    fn enqueue_var(&mut self, v: &mut Var) -> ();
    fn clause_queue_len(&self) -> usize;
    fn var_queue_len(&self) -> usize;
}

/// Literal eliminator
pub struct Eliminator {
    pub eliminated_vars: usize,
    pub use_elim: bool,
    pub use_simplification: bool,
    pub last_invocatiton: usize,
    next_invocation: usize,
    pub n_touched: usize,
    merges: usize,
    clause_queue: Vec<ClauseId>,
    pub var_queue: Vec<VarId>,
    bwdsub_assigns: usize,
    // working place
    elim_clauses: Vec<Lit>,
    /// Variables are not eliminated if it produces a resolvent with a length above this limit.
    /// 0 means no limit.
    clause_lim: usize,
    subsumption_lim: usize,
    clause_queue_threshold: usize,
    var_queue_threshold: usize,
}

const SUBSUMPTION_SIZE: usize = 30;
const SUBSUMPITON_GROW_LIMIT: usize = 0;
const BACKWORD_SUBSUMPTION_THRESHOLD: usize = 1_000_000; // 10_000;
const CLAUSE_QUEUE_THRESHOD: usize = 1_000_000; // 1_000;
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
            last_invocatiton: 0,
            next_invocation: 32,
            clause_queue_threshold: CLAUSE_QUEUE_THRESHOD,
            var_queue_threshold: VAR_QUEUE_THRESHOLD,
        }
    }
    fn enqueue_clause(&mut self, cid: ClauseId, ch: &mut ClauseHead) -> () {
        if !self.use_elim || self.clause_queue_threshold == 0 {
            // println!("{} is not enqueued", cid2fmt(cid));
            return;
        }
        let rank = ch.rank as f64;
        if !ch.get_flag(ClauseFlag::Enqueued) {
            let accept = if self.clause_queue.len() <= 256 {
                rank
            } else {
                4.8 - ((self.clause_queue.len() as f64).log(2.0) - 8.0)
            };
            if rank <= accept {
                self.clause_queue.push(cid);
                // println!("increment {}", self.eliminator.clause_queue.len());
                ch.set_flag(ClauseFlag::Enqueued, true);
                self.clause_queue_threshold -= 1;
            }
        }
    }
    fn enqueue_var(&mut self, v: &mut Var) -> () {
        if !self.use_elim || self.var_queue_threshold == 0 {
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

#[test]
impl fmt::Display for Eliminator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            " - n_touched {}\n - clause_queue {:?}\n - heap {:?}",
            self.n_touched, self.clause_queue, self.var_queue,
        )
    }
}

impl ClauseElimination for Solver {
    fn check_eliminator(&self) -> bool {
        // clause_queue should be clear.
        // debug_assert!(self.eliminator.clause_queue.is_empty());
        // all elements in occur_lists exist.
        for v in &self.vars {
            for c in &v.pos_occurs {
                let ch = clause!(self.cp, c);
                if ch.lit[0] <= GARBAGE_LIT || ch.lit[1] <= GARBAGE_LIT {
                    panic!("panic {:#}", ch);
                }
            }
            for c in &v.neg_occurs {
                let ch = clause!(self.cp, c);
                if ch.lit[0] <= GARBAGE_LIT || ch.lit[1] <= GARBAGE_LIT {
                    panic!("panic {:#}", ch);
                }
            }
        }
        // all caulses are registered in corresponding occur_lists
        let kinds = [
            ClauseKind::Binclause,
            ClauseKind::Removable,
            ClauseKind::Permanent,
        ];
        for kind in &kinds {
            for (ci, ch) in self.cp[*kind as usize].head.iter().enumerate().skip(1) {
                let cid = kind.id_from(ci);
                if ch.lit[0] == RECYCLE_LIT && ch.lit[1] == RECYCLE_LIT {
                    continue;
                }
                for l in &ch.lits {
                    let v = l.vi();
                    if l.positive() {
                        if !self.vars[v].pos_occurs.contains(&cid) {
                            panic!("aaa {} {:#}", cid2fmt(cid), ch);
                        }
                    } else {
                        if !self.vars[v].neg_occurs.contains(&cid) {
                            panic!("aaa {} {:#}", cid2fmt(cid), ch);
                        }
                    }
                }
            }
        }
        return true;
    }
}

impl Solver {
    /// 5. strengthenClause
    /// returns false if inconsistent
    /// - calls `enqueue_clause`
    /// - calls `enqueue_var`
    pub fn strengthen_clause(&mut self, cid: ClauseId, l: Lit) -> bool {
        debug_assert!(!clause!(self.cp, cid).get_flag(ClauseFlag::Dead));
        debug_assert!(!clause!(self.cp, cid).get_flag(ClauseFlag::Locked));
        debug_assert!(1 < clause!(self.cp, cid).lits.len());
        self.cp[cid.to_kind()].touched[l as usize] = true;
        self.cp[cid.to_kind()].touched[l.negate() as usize] = true;
        // println!("STRENGTHEN_CLAUSE {}", cid2fmt(cid));
        debug_assert_ne!(cid, NULL_CLAUSE);
        if self.strengthen(cid, l) {
            // since changing a literal in `lit` requires updating a next_watcher,
            // it's muth easier to hold the literal to be propagated in body.lits[0]
            // let c0 = clause_head!(self.cp, cid).lit[0];
            let c0 = clause!(self.cp, cid).lits[0];
            debug_assert!(1 == clause!(self.cp, cid).lits.len());
            debug_assert!(c0 == clause!(self.cp, cid).lits[0]);
            // println!("cid {} {:?} became a unit clause as c0 {}, l {}", cid2fmt(cid), vec2int(&clause_body!(self.cp, cid).lits), c0.int(), l.int());
            debug_assert_ne!(c0, l);
            // println!("{} is removed and its first literal {} is enqueued.", cid2fmt(cid), c0.int());
            self.remove_clause(cid);
            self.vars[..].detach_clause(cid, clause!(self.cp, cid), &mut self.eliminator);
            if self.enqueue(c0, NULL_CLAUSE) && self.propagate_0() == NULL_CLAUSE {
                // self.cp[cid.to_kind()].touched[c0 as usize] = true;
                self.cp[cid.to_kind()].touched[c0.negate() as usize] = true;
                true
            } else {
                // println!("{:?}", self.vars[c0.vi()]);
                self.ok = false;
                false
            }
        } else {
            // println!("cid {} drops literal {}", cid2fmt(cid), l.int());
            debug_assert!(1 < clause!(self.cp, cid).lits.len());
            self.eliminator.enqueue_clause(cid, clause_mut!(self.cp, cid));
            true
        }
    }
    /// 6. merge(1)
    /// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
    pub fn merge(&mut self, cp: ClauseId, cq: ClauseId, v: VarId) -> Option<Vec<Lit>> {
        let mut vec: Vec<Lit> = Vec::new();
        self.eliminator.merges += 1;
        let pqb = clause!(self.cp, cp);
        let qpb = clause!(self.cp, cq);
        let ps_smallest = pqb.lits.len() < qpb.lits.len();
        let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
        // println!(" -  {:?}{:?} & {:?}{:?}", vec2int(&ph.lit),vec2int(&pb.lits),vec2int(&qh.lit),vec2int(&qb.lits));
        'next_literal: for l in &qb.lits {
            if l.vi() != v {
                for j in &pb.lits {
                    if j.vi() == l.vi() {
                        if j.negate() == *l {
                            return None;
                        } else {
                            continue 'next_literal;
                        }
                    }
                }
                vec.push(*l);
            }
        }
        for l in &pb.lits {
            if l.vi() != v {
                vec.push(*l);
            }
        }
        // println!("merge generated {:?} from {} and {} to eliminate {}", vec2int(vec.clone()), p, q, v);
        Some(vec)
    }
    /// 7. merge(2)
    /// Returns **false** if one of the clauses is always satisfied.
    pub fn check_to_merge(&mut self, cp: ClauseId, cq: ClauseId, v: VarId) -> (bool, usize) {
        self.eliminator.merges += 1;
        let pqb = clause!(self.cp, cp);
        let qpb = clause!(self.cp, cq);
        let ps_smallest = pqb.lits.len() < qpb.lits.len();
        let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
        let mut size = pb.lits.len() + 1;
        'next_literal: for l in &qb.lits {
            if l.vi() != v {
                for j in &pb.lits {
                    if j.vi() == l.vi() {
                        if j.negate() == *l {
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
            unsafe {
                let mut best = 0;
                let unilits: [Lit; 1];
                let mut lits: &[Lit];
                // let ch = clause_head_mut!(self.cp, cid) as *mut ClauseHead;
                if cid.to_kind() == ClauseKind::Uniclause as usize {
                    best = (cid.to_index() as Lit).vi();
                    unilits = [cid.to_index() as Lit; 1];
                    lits = &unilits;
                } else {
                    let ch = clause_mut!(self.cp, cid) as *mut ClauseHead;
                    (*ch).set_flag(ClauseFlag::Enqueued, false);
                    lits = &(*ch).lits;
                    if (*ch).get_flag(ClauseFlag::Dead) || BACKWORD_SUBSUMPTION_THRESHOLD < cnt {
                        continue;
                    }
                    let mut tmp = 1_000_000;
                    for l in &(*ch).lits {
                        let v = &self.vars[l.vi()];
                        let nsum = v.pos_occurs.len().min(v.neg_occurs.len());
                        if !v.eliminated && 0 < v.level && nsum < tmp {
                            best = l.vi();
                            tmp = nsum;
                        }
                    }
                }
                if best == 0 || self.vars[best].eliminated {
                    continue;
                }
                for p in 0..2 {
                    let cs = if p == 0 {
                        &mut self.vars[best].pos_occurs as *mut Vec<ClauseId>
                    } else {
                        &mut self.vars[best].neg_occurs as *mut Vec<ClauseId>
                    };
                    cnt += (*cs).len();
                    for di in &*cs {
                        let db = clause!(self.cp, di) as *const ClauseHead;
                        debug_assert!(
                            (!(*db).get_flag(ClauseFlag::Locked))
                                || (*db).get_flag(ClauseFlag::Dead)
                        );
                        if !(*db).get_flag(ClauseFlag::Dead)
                            && *di != cid
                            && lits.len() <= SUBSUMPTION_SIZE
                            && (*db).lits.len() <= SUBSUMPTION_SIZE
                            && (self.eliminator.subsumption_lim == 0
                                || lits.len() + (*db).lits.len() <= self.eliminator.subsumption_lim)
                        {
                            match self.subsume(cid, *di) {
                                Some(NULL_LIT) => {
                                    subsumed += 1;
                                    if cid.to_kind() == ClauseKind::Removable as usize
                                        && di.to_kind() == ClauseKind::Removable as usize
                                    {
                                        // println!("BackSubsC    => {} {:#} subsumed completely by {} {:#}",
                                        //          cid2fmt(*di),
                                        //          *db,
                                        //          cid2fmt(cid),
                                        //          *clause_body!(self.cp, cid),
                                        // );
                                        self.remove_clause(*di);
                                        self.vars[..].detach_clause(*di, clause!(self.cp, cid), &mut self.eliminator);
                                    } //else {
                                      // println!("backward_subsumption_check tries to delete a permanent clause {} {:#}",
                                      //          cid2fmt(*di),
                                      //          clause_body!(self.cp, *di));
                                      // TODO: move the cid to Permanent
                                      //}
                                }
                                Some(l) => {
                                    self.cp[di.to_kind()].touched[l as usize] = true;
                                    self.cp[di.to_kind()].touched[l.negate() as usize] = true;
                                    // let xb = &clause_body!(self.cp, *di);
                                    // println!("BackSubsC    => subsumed {} from {} and {} {:#}", l.int(), cid2fmt(cid), cid2fmt(*di), xb);
                                    deleted_literals += 1;
                                    // println!("cancel true path");
                                    // continue;
                                    if !self.strengthen_clause(*di, l.negate()) {
                                        return false;
                                    }
                                    self.eliminator.enqueue_var(&mut self.vars[l.vi()]);
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
        let ch = clause!(self.cp, cid);
        debug_assert!(0 < ch.lits.len());
        for l in &ch.lits {
            vec.push(*l as u32);
            if l.vi() == vi {
                let index = vec.len() - 1;
                debug_assert_eq!(vec[index], *l);
                debug_assert_eq!(vec[index].vi(), vi);
                // swap the first literal with the 'v'. So that the literal containing 'v' will occur first in the clause.
                vec.swap(index, first);
            }
        }
        // Store the length of the clause last:
        debug_assert_eq!(vec[first].vi(), vi);
        vec.push(ch.lits.len() as Lit);
        // println!("make_eliminated_clause: eliminate({}) clause {:?}", vi, vec2int(&ch.lits));
    }
    /// 15. eliminateVar
    /// returns false if solver is in inconsistent
    pub fn eliminate_var(&mut self, v: VarId) -> bool {
        if self.vars[v].assign != BOTTOM {
            return true;
        }
        debug_assert!(!self.vars[v].eliminated);
        {
            // count only alive clauses
            let Solver {
                ref mut vars,
                ref cp,
                ..
            } = self;
            vars[v]
                .pos_occurs
                .retain(|&c| !clause!(cp, c).get_flag(ClauseFlag::Dead));
            vars[v]
                .pos_occurs
                .retain(|&c| !clause!(cp, c).get_flag(ClauseFlag::Dead));
        }
        let pos = &self.vars[v].pos_occurs as *const Vec<ClauseId>;
        let neg = &self.vars[v].neg_occurs as *const Vec<ClauseId>;
        unsafe {
            // Check wether the increase in number of clauses stays within the allowed ('grow').
            // Moreover, no clause must exceed the limit on the maximal clause size (if it is set).
            if (*pos).len() == 0 && 0 == (*neg).len() {
                return true;
            }
            if (*pos).len() == 0 && 0 < (*neg).len() {
                // println!("-v {} p {} n {}", v, (*pos).len(), (*neg).len());
                if !self.enqueue(v.lit(LFALSE), NULL_CLAUSE) || self.propagate_0() != NULL_CLAUSE {
                    self.ok = false;
                    return false;
                }
                return true;
            }
            if (*neg).len() == 0 && (*pos).len() == 0 {
                // println!("+v {} p {} n {}", v, (*pos).len(), (*neg).len());
                if !self.enqueue(v.lit(LTRUE), NULL_CLAUSE) || self.propagate_0() != NULL_CLAUSE {
                    self.ok = false;
                    // panic!("eliminate_var: failed to enqueue & propagate");
                    return false;
                }
                return true;
            }
            let clslen = (*pos).len() + (*neg).len();
            let mut cnt = 0;
            for lit_pos in &*pos {
                if clause!(self.cp, lit_pos).get_flag(ClauseFlag::Dead) {
                    continue;
                }
                for lit_neg in &*neg {
                    if clause!(self.cp, lit_neg).get_flag(ClauseFlag::Dead) {
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
            debug_assert!(!self.vars[v].eliminated);
            self.vars[v].eliminated = true;
            let cid = self.vars[v].reason;
            debug_assert_eq!(cid, NULL_CLAUSE);
            // println!("- eliminate var: {:>8} (+{:<4} -{:<4}); {:?}", v, (*pos).len(), (*neg).len(), self.vars[v]);
            // setDecisionVar(v, false);
            self.eliminator.eliminated_vars += 1;
            {
                let tmp = &mut self.eliminator.elim_clauses as *mut Vec<Lit>;
                if (*neg).len() < (*pos).len() {
                    for cid in &*neg {
                        if clause!(self.cp, cid).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
                        self.make_eliminated_clause(&mut (*tmp), v, *cid);
                        self.cp[cid.to_kind() as usize].touched[v.lit(LTRUE) as usize] = true;
                        self.cp[cid.to_kind() as usize].touched[v.lit(LFALSE) as usize] = true;
                    }
                    self.make_eliminating_unit_clause(&mut (*tmp), v.lit(LTRUE));
                // println!("eliminate unit clause {}", v.lit(LFALSE).int());
                } else {
                    for cid in &*pos {
                        if clause!(self.cp, cid).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
                        self.make_eliminated_clause(&mut (*tmp), v, *cid);
                        self.cp[cid.to_kind() as usize].touched[v.lit(LTRUE) as usize] = true;
                        self.cp[cid.to_kind() as usize].touched[v.lit(LFALSE) as usize] = true;
                    }
                    self.make_eliminating_unit_clause(&mut (*tmp), v.lit(LFALSE));
                    // println!("eliminate unit clause {}", v.lit(LTRUE).int());
                }
            }
            // Produce clauses in cross product:
            {
                for p in &*pos {
                    if clause!(self.cp, p).get_flag(ClauseFlag::Dead) {
                        continue;
                    }
                    let act_p = clause!(self.cp, p).activity;
                    let rank_p = clause!(self.cp, p).rank;
                    for n in &*neg {
                        if clause!(self.cp, n).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
                        if let Some(vec) = self.merge(*p, *n, v) {
                            // println!("eliminator replaces {} with a cross product {:?}", cid2fmt(*p), vec2int(&vec));
                            match vec.len() {
                                0 => {
                                    panic!("zero");
                                }
                                1 => {
                                    // println!(
                                    //     "eliminate_var: grounds {} from {}{:?} and {}{:?}",
                                    //     vec[0].int(),
                                    //     cid2fmt(*p),
                                    //     vec2int(&clause_body!(self.cp, *p).lits),
                                    //     cid2fmt(*n),
                                    //     vec2int(&clause_body!(self.cp, *n).lits)
                                    // );
                                    if !self.enqueue(vec[0], NULL_CLAUSE) {
                                        self.ok = false;
                                        // panic!("eliminate_var: failed to enqueue & propagate");
                                        return false;
                                    }
                                }
                                _ => {
                                    if p.to_kind() == ClauseKind::Removable as usize
                                        && n.to_kind() == ClauseKind::Removable as usize
                                    {
                                        let act_n = clause!(self.cp, n).activity;
                                        let rank_n = clause!(self.cp, n).rank;
                                        let new =
                                            self.add_clause(&mut vec.to_vec(), rank_p.min(rank_n));
                                        clause_mut!(self.cp, new).activity = act_p.max(act_n);
                                    } else {
                                        self.add_clause(&mut vec.to_vec(), 0);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            for i in 0..2 {
                for cid in if i == 0 {
                    &mut self.vars[v].pos_occurs
                } else {
                    &mut self.vars[v].neg_occurs
                } {
                    clause_mut!(self.cp, *cid).set_flag(ClauseFlag::Dead, true);
                    let w0;
                    let w1;
                    {
                        let ch = clause!(self.cp, *cid);
                        w0 = ch.lit[0].negate();
                        w1 = ch.lit[1].negate();
                    }
                    debug_assert!(w0 != 0 && w1 != 0);
                    self.cp[cid.to_kind()].touched[w0 as usize] = true;
                    self.cp[cid.to_kind()].touched[w1 as usize] = true;
                }
                // self.cp[cid.to_kind()].touched[v.lit(LTRUE) as usize] = true;
                // self.cp[cid.to_kind()].touched[v.lit(LFALSE) as usize] = true;
            }
            self.vars[v].pos_occurs.clear();
            self.vars[v].neg_occurs.clear();
            if self.propagate_0() != NULL_CLAUSE {
                self.ok = false;
                return false;
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
        // println!("extend_model {:?}", &self.eliminator.elim_clauses);
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
            debug_assert!(width == 1);
            let l = self.eliminator.elim_clauses[i];
            // debug_assert!(model[l.vi() - 1] != l.negate().int());
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
        if !self.eliminator.use_elim {
            return;
        }
        if self.eliminator.next_invocation < self.eliminator.var_queue.len() {
            self.eliminator.clause_queue.clear();
            for v in &self.eliminator.var_queue {
                self.vars[*v].enqueued = false;
            }
            self.eliminator.var_queue.clear();
            return;
        }
        // self.eliminator.next_invocation += 2;
        // println!("eliminate: clause_queue {}", self.eliminator.clause_queue.len());
        // println!("clause_queue {:?}", self.eliminator.clause_queue);
        // println!("var_queue {:?}", self.eliminator.var_queue);
        // println!("n_touched {}", self.eliminator.n_touched);
        // self.build_occurence_list();
        // for i in 1..4 { println!("eliminate report: v{} => {},{}", i, self.vars[i].num_occurs, self.vars[i].occurs.len()); }
        // self.eliminator.clause_queue.clear();
        'perform: while self.eliminator.bwdsub_assigns < self.trail.len()
            || !self.eliminator.var_queue.is_empty()
            || !self.eliminator.clause_queue.is_empty()
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
                if self.vars[elim].eliminated || self.vars[elim].assign != BOTTOM {
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
        debug_assert!(other.to_kind() != ClauseKind::Uniclause as usize);
        // if other.to_kind() == ClauseKind::Uniclause as usize {
        //     panic!("unexpected path!");
        // }
        if cid.to_kind() == ClauseKind::Uniclause as usize {
            let l = cid.to_index() as Lit;
            let oh = clause!(self.cp, other);
            for lo in &oh.lits {
                if l == lo.negate() {
                    return Some(l);
                }
            }
            return None;
        }
        // println!("subsume {} = {}:{}", cid, cid.to_kind(), cid.to_index());
        let mut ret: Lit = NULL_LIT;
        let ch = clause!(self.cp, cid);
        let ob = clause!(self.cp, other);
        debug_assert!(ob.lits.contains(&clause!(self.cp, other).lit[0]));
        debug_assert!(ob.lits.contains(&clause!(self.cp, other).lit[1]));
        'next: for l in &ch.lits {
            for lo in &ob.lits {
                if *l == *lo {
                    continue 'next;
                } else if ret == NULL_LIT && *l == lo.negate() {
                    ret = *l;
                    continue 'next;
                }
            }
            return None;
        }
        Some(ret)
    }

    /// removes Lit `p` from Clause *self*. This is an O(n) function!
    /// returns true if the clause became a unit clause.
    /// Called only from strengthen_clause
    pub fn strengthen(&mut self, cid: ClauseId, p: Lit) -> bool {
        debug_assert!(!clause!(self.cp, cid).get_flag(ClauseFlag::Dead));
        debug_assert!(1 < clause!(self.cp, cid).lits.len());
        let cix = cid.to_index();
        let ClausePartition {
            ref mut head,
            ref mut watcher,
            ..
        } = self.cp[cid.to_kind()];
        unsafe {
            let cix = cid.to_index();
            let ch = &mut head[cix] as *mut ClauseHead;
            // debug_assert!((*ch).lits.contains(&p));
            // debug_assert!(1 < (*ch).lits.len());
            {
                let v = &mut self.vars[p.vi()];
                if p.positive() {
                    // debug_assert!(v.pos_occurs.contains(&cid));
                    v.pos_occurs.retain(|&c| c != cid);
                } else {
                    // debug_assert!(v.neg_occurs.contains(&cid));
                    v.neg_occurs.retain(|&c| c != cid);
                }
            }
            if (*ch).get_flag(ClauseFlag::Dead) {
                return false;
            }
            if (*ch).lit[0] == p || (*ch).lit[1] == p {
                debug_assert!((*ch).lits[0] == p || (*ch).lits[1] == p);
                // update lit, next_watcher, and lits
                let hi = ((*ch).lit[0] != p) as usize;
                debug_assert!((*ch).lit[hi] == p);
                let bi = ((*ch).lits[0] != p) as usize;
                debug_assert!((*ch).lits[bi] == p);
                (*ch).lits.swap_remove(bi);
                if (*ch).lits.len() == 1 {
                    if hi == 1 {
                        (*ch).lit.swap(0, 1);
                        (*ch).next_watcher.swap(0, 1);
                    }
                    // debug_assert!((*ch).lit[0] == p);
                    // debug_assert!((*ch).lits[0] != p);
                    // (*ch).lits[0] = (*ch).lit[0];
                    // (*ch).lit[0] = (*ch).lits[0];
                    // (*ch).lit[1] = (*ch).lits[0].negate();
                    // debug_assert!((*ch).lit[0] != p);
                    // debug_assert!(1 < (*ch).lit[0]);
                    // debug_assert!((*ch).lit[1] != p);
                    // stores the last literal in lits, while leaving `lit` as is.
                    debug_assert!((*ch).lits[0] != p);
                    // println!("unit {} elimanated {}", (*ch).lits[0].int(), p.int());
                    return true;
                }
                let new_lit = (*ch).lits[bi];
                debug_assert_ne!(new_lit, p);
                let next_clause = (*ch).next_watcher[hi];
                // pointer update
                {
                    let mut ptr = &mut watcher[p.negate() as usize] as *mut ClauseIndex;
                    while *ptr != NULL_CLAUSE {
                        if *ptr == cix {
                            *ptr = next_clause;
                            break;
                        }
                        let i = (head[*ptr].lit[0] != p) as usize;
                        debug_assert_eq!(head[*ptr].lit[i], p);
                        ptr = &mut head[*ptr].next_watcher[i];
                    }
                }
                (*ch).lit[hi] = new_lit;
                (*ch).next_watcher[hi] = watcher[new_lit.negate() as usize];
                watcher[new_lit.negate() as usize] = cix;
                if (*ch).lits.len() == 1 {
                    debug_assert!((*ch).lit[1] != new_lit);
                    true
                } else {
                    false
                }
            } else {
                debug_assert!((*ch).lit[0] != p.negate() && (*ch).lit[1] != p.negate());
                (*ch).lits.retain(|&x| x != p);
                false
            }
        }
    }
}

#![allow(unreachable_code)]
#![allow(unused_mut)]
#![allow(unused_variables)]
use clause::{
    cid2fmt, ClauseBody, ClauseFlag, ClauseHead, ClauseIdIndexEncoding, ClauseIndex, ClauseKind,
    ClauseManagement, ClausePartition,
};
use solver::{Solver, CDCL};
use std::fmt;
use types::*;
use var::Var;

// for Solver
pub trait ClauseElimination {
    fn eliminator_register_clause(&mut self, cid: ClauseId, rank: usize, ignorable: bool) -> ();
    fn eliminator_enqueue_clause(&mut self, cid: ClauseId) -> ();
    fn eliminator_enqueue_var(&mut self, vi: VarId) -> ();
    fn eliminator_unregister_clause(&mut self, cid: ClauseId) -> ();
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
            clause_queue_threshold: CLAUSE_QUEUE_THRESHOD,
            var_queue_threshold: VAR_QUEUE_THRESHOLD,
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
    fn eliminator_register_clause(&mut self, cid: ClauseId, rank: usize, ignorable: bool) -> () {
        if !self.eliminator.use_elim {
            return;
        }
        {
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
        if !ignorable {
            self.eliminator_enqueue_clause(cid);
        }
    }
    fn eliminator_enqueue_clause(&mut self, cid: ClauseId) -> () {
        if !self.eliminator.use_elim || self.eliminator.clause_queue_threshold == 0 {
            // println!("{} is not enqueued", cid2fmt(cid));
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
        if !self.eliminator.use_elim {
            return;
        }
        self.eliminator.enqueue_var(&mut self.vars[vi])
    }
    fn eliminator_unregister_clause(&mut self, cid: ClauseId) -> () {
        debug_assert!(clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead));
        if self.eliminator.use_elim {
            for l in &clause_body!(self.cp, cid).lits {
                let v = &mut self.vars[l.vi()];
                if !v.eliminated {
                    let xx = v.pos_occurs.len() + v.neg_occurs.len();
                    if l.positive() {
                        v.pos_occurs.retain(|&cj| cid != cj);
                    } else {
                        v.neg_occurs.retain(|&cj| cid != cj);
                    }
                    let xy = v.pos_occurs.len() + v.neg_occurs.len();
                    self.eliminator.enqueue_var(v);
                }
            }
        }
    }
}

impl Solver {
    /// 5. strengthenClause
    /// returns false if inconsistent
    /// - calls `enqueue_clause`
    /// - calls `enqueue_var`
    pub fn strengthen_clause(&mut self, cid: ClauseId, l: Lit) -> bool {
        debug_assert!(!clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead));
        debug_assert!(!clause_body!(self.cp, cid).get_flag(ClauseFlag::Locked));
        debug_assert!(1 < clause_body!(self.cp, cid).lits.len());
        self.cp[cid.to_kind()].touched[l as usize] = true;
        self.cp[cid.to_kind()].touched[l.negate() as usize] = true;
        // println!("STRENGTHEN_CLAUSE {}:{}", cid2fmt(cid));
        debug_assert_ne!(cid, NULL_CLAUSE);
        if self.strengthen(cid, l) {
            let c0 = clause_head!(self.cp, cid).lit[0];
            debug_assert!(1 == clause_body!(self.cp, cid).lits.len());
            debug_assert!(c0 == clause_body!(self.cp, cid).lits[0]);
            // println!("cid {} {:?} became a unit clause as c0 {}, l {}", cid2fmt(cid), vec2int(&clause_body!(self.cp, cid).lits), c0.int(), l.int());
            debug_assert_ne!(c0, l);
            // println!("{} is removed and its first literal {} is enqueued.", cid2fmt(cid), c0.int());
            self.remove_clause(cid);
            self.eliminator_unregister_clause(cid);
            // before the following propagate, we need to clean garbages.
            // これまずくないか? self.cp[cid.to_kind()].garbage_collect(&mut self.vars, &mut self.eliminator);
            // println!("STRENGTHEN_CLAUSE ENQUEUE {}", c0);
            if self.enqueue(c0, NULL_CLAUSE) && self.propagate() == NULL_CLAUSE {
                // self.cp[cid.to_kind()].touched[c0 as usize] = true;
                self.cp[cid.to_kind()].touched[c0.negate() as usize] = true;
                true
            } else {
                //println!("{:?}", self.vars[c0.vi()]);
                panic!(
                    "Conflicting Enqueue:: A l {}, c0 {}, {:#} {:#}",
                    l.int(),
                    c0.int(),
                    clause_head!(self.cp, cid),
                    clause_body!(self.cp, cid)
                );
                self.ok = false;
                false
            }
        } else {
            // println!("cid {} drops literal {}", cid2fmt(cid), l.int());
            debug_assert!(1 < clause_body!(self.cp, cid).lits.len());
            self.eliminator_enqueue_clause(cid);
            true
        }
    }
    /// 6. merge(1)
    /// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
    pub fn merge(&mut self, cp: ClauseId, cq: ClauseId, v: VarId) -> Option<Vec<Lit>> {
        let mut vec: Vec<Lit> = Vec::new();
        self.eliminator.merges += 1;
        let pqb = clause_body!(self.cp, cp);
        let qpb = clause_body!(self.cp, cq);
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
        let pqb = clause_body!(self.cp, cp);
        let qpb = clause_body!(self.cp, cq);
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
            // println!("bsc remain clauses {} vars {}", self.eliminator.clause_queue.len(), self.eliminator.var_queue.len());
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
                    let cb = clause_body_mut!(self.cp, cid) as *mut ClauseBody;
                    (*cb).set_flag(ClauseFlag::Enqueued, false);
                    lits = &(*cb).lits;
                    if (*cb).get_flag(ClauseFlag::Dead) || BACKWORD_SUBSUMPTION_THRESHOLD < cnt {
                        continue;
                    }
                    let mut tmp = 1_000_000;
                    for l in &(*cb).lits {
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
                        let db = clause_body!(self.cp, di) as *const ClauseBody;
                        // if (*db).get_flag(ClauseFlag::Locked) && !(*db).get_flag(ClauseFlag::Dead) {
                        //     println!("di {} body {:#}, lits[0]vi {}",
                        //              cid2fmt(*di),
                        //              *db,
                        //              cid2fmt(self.vars[(*db).lits[0].vi()].reason),
                        //              );
                        // }
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
                            // ここから先を潰すとvalid answer
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
                                        self.eliminator_unregister_clause(*di);
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
                                    self.eliminator_enqueue_var(l.vi());
                                    // if self.propagate() != NULL_CLAUSE {
                                    //     self.ok = false;
                                    //     panic!("@backward_subsumption_check called propagate and failed!");
                                    // }
                                }
                                None => {}
                            }
                        }
                    }
                }
                // if self.q_head < self.trail.len() {
                //     panic!("wwwwwwwwwwwwwww");
                // }
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
        debug_assert!(0 < cb.lits.len());
        for l in &cb.lits {
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
        if vec[first].vi() != vi {
            panic!("ooo {:?} by {}", vec2int(&cb.lits), vi);
        }
        debug_assert_eq!(vec[first].vi(), vi);
        vec.push(cb.lits.len() as Lit);
        // println!("make_eliminated_clause: eliminate({}) clause {:?}", vi, vec2int(&cb.lits));
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
                .retain(|&c| !clause_body!(cp, c).get_flag(ClauseFlag::Dead));
            vars[v]
                .pos_occurs
                .retain(|&c| !clause_body!(cp, c).get_flag(ClauseFlag::Dead));
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
                if !self.enqueue(v.lit(LFALSE), NULL_CLAUSE) || self.propagate() != NULL_CLAUSE {
                    self.ok = false;
                    return false;
                }
                return true;
            }
            if (*neg).len() == 0 && (*pos).len() == 0 {
                // println!("+v {} p {} n {}", v, (*pos).len(), (*neg).len());
                if !self.enqueue(v.lit(LTRUE), NULL_CLAUSE) || self.propagate() != NULL_CLAUSE {
                    self.ok = false;
                    // panic!("eliminate_var: failed to enqueue & propagate");
                    return false;
                }
                return true;
            }
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
                        if clause_body!(self.cp, cid).lits.contains(&v.lit(LTRUE)) {
                            panic!(
                                "ultra panic {} {:?}.",
                                cid2fmt(*cid),
                                vec2int(&clause_body!(self.cp, cid).lits)
                            );
                        }
                        if !clause_body!(self.cp, cid).lits.contains(&v.lit(LFALSE)) {
                            panic!(
                                "ultra panic {} {:?}.",
                                cid2fmt(*cid),
                                vec2int(&clause_body!(self.cp, cid).lits)
                            );
                        }
                        if clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead) {
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
                        if clause_body!(self.cp, cid).lits.contains(&v.lit(LFALSE)) {
                            panic!(
                                "ultra panic {} {:?}.",
                                cid2fmt(*cid),
                                vec2int(&clause_body!(self.cp, cid).lits)
                            );
                        }
                        if !clause_body!(self.cp, cid).lits.contains(&v.lit(LTRUE)) {
                            panic!(
                                "ultra panic {} {:?}.",
                                cid2fmt(*cid),
                                vec2int(&clause_body!(self.cp, cid).lits)
                            );
                        }
                        if clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead) {
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
                    if clause_body!(self.cp, p).get_flag(ClauseFlag::Dead) {
                        continue;
                    }
                    for n in &*neg {
                        if clause_body!(self.cp, n).get_flag(ClauseFlag::Dead) {
                            continue;
                        }
                        if let Some(vec) = self.merge(*p, *n, v) {
                            // println!("eliminator replaces {} with a cross product {:?}", cid2fmt(*p), vec2int(&vec));
                            match vec.len() {
                                0 => {
                                    panic!("zero");
                                }
                                1 => {
                                    // println!("eliminate_var: grounds {} from {}{:?} and {}{:?}", vec[0].int(), cid2fmt(*p), vec2int(&clause_body!(self.cp, *p).lits), cid2fmt(*n), vec2int(&clause_body!(self.cp, *n).lits));
                                    if !self.enqueue(vec[0], NULL_CLAUSE)
                                        || self.propagate() != NULL_CLAUSE
                                    {
                                        self.ok = false;
                                        panic!("eliminate_var: failed to enqueue & propagate");
                                    }
                                }
                                _ => {
                                    self.add_clause(&mut vec.to_vec(), 0);
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
                    clause_body_mut!(self.cp, *cid).set_flag(ClauseFlag::Dead, true);
                    let w0;
                    let w1;
                    {
                        let ch = clause_head!(self.cp, *cid);
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
            //{
            //    // v should be disappeared from the problem!
            //    let kinds = [ClauseKind::Binclause, ClauseKind::Removable, ClauseKind::Permanent];
            //    for kind in &kinds {
            //        for (i, b) in self.cp[*kind as usize].body.iter().enumerate().skip(1) {
            //            if b.lits.contains(&v.lit(LTRUE)) || b.lits.contains(&v.lit(LFALSE)) {
            //                if !b.get_flag(ClauseFlag::Dead) {
            //                    panic!("FOUND: {:#} in {:?}{}/{:?}", v, kind, i, vec2int(&b.lits));
            //                }
            //            }
            //        }
            //    }
            //}
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
            // assert!(model[l.vi() - 1] != l.negate().int());
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
        // println!("eliminate: clause_queue {}", self.eliminator.clause_queue.len());
        // println!("clause_queue {:?}", self.eliminator.clause_queue);
        // println!("var_queue {:?}", self.eliminator.var_queue);
        // println!("n_touched {}", self.eliminator.n_touched);
        // self.build_occurence_list();
        // for i in 1..4 { println!("eliminate report: v{} => {},{}", i, self.vars[i].num_occurs, self.vars[i].occurs.len()); }
        // self.eliminator.clause_queue.clear();
        'perform: while self.eliminator.bwdsub_assigns < self.trail.len()
            || !self.eliminator.var_queue.is_empty()
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
        if other.to_kind() == ClauseKind::Uniclause as usize {
            panic!("unexpected path!");
        }
        if cid.to_kind() == ClauseKind::Uniclause as usize {
            let l = cid.to_index() as Lit;
            let oh = clause_head!(self.cp, other);
            let ob = clause_body!(self.cp, other);
            for lo in &ob.lits {
                if l == lo.negate() {
                    return Some(l);
                }
            }
            return None;
        }
        // println!("subsume {} = {}:{}", cid, cid.to_kind(), cid.to_index());
        let mut ret: Lit = NULL_LIT;
        let cb = clause_body!(self.cp, cid);
        let ob = clause_body!(self.cp, other);
        if !ob.lits.contains(&clause_head!(self.cp, other).lit[0]) {
            panic!(
                "@subsume: the 1st literal of the other clause is ill-formed {} {:#}!",
                cid2fmt(other),
                ob
            );
        }
        if !ob.lits.contains(&clause_head!(self.cp, other).lit[1]) {
            panic!(
                "@subsume: the 2nd literal of the other clause is ill-formed {} {:#}!",
                cid2fmt(other),
                ob
            );
        }
        'next: for l in &cb.lits {
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
        debug_assert!(!clause_body!(self.cp, cid).get_flag(ClauseFlag::Dead));
        let cix = cid.to_index();
        let ClausePartition {
            ref mut head,
            ref mut body,
            ref mut watcher,
            ..
        } = self.cp[cid.to_kind()];
        unsafe {
            let cix = cid.to_index();
            let ch = &mut head[cix] as *mut ClauseHead;
            let cb = &mut body[cix] as *mut ClauseBody;
            if (*cb).get_flag(ClauseFlag::Dead) {
                return false;
            }
            {
                let v = &mut self.vars[p.vi()];
                if p.positive() {
                    v.pos_occurs.retain(|&c| c != cid);
                } else {
                    v.neg_occurs.retain(|&c| c != cid);
                }
            }
            if (*ch).lit[0] == p || (*ch).lit[1] == p {
                debug_assert!((*cb).lits[0] == p || (*cb).lits[1] == p);
                // update lit, next_watcher, and lits
                let hi = ((*ch).lit[0] != p) as usize;
                debug_assert!((*ch).lit[hi] == p);
                let bi = ((*cb).lits[0] != p) as usize;
                debug_assert!((*cb).lits[bi] == p);
                (*cb).lits.swap_remove(bi);
                if (*cb).lits.len() == 1 {
                    if hi == 0 {
                        (*ch).lit.swap(0, 1);
                        (*ch).next_watcher.swap(0, 1);
                    }
                    if bi == 1 {
                        // panic!("p {}, l0 {}, UNITCLAUSE {} {:#} {:#}", p.int(), (*ch).lit[0].int(), cid2fmt(cid), *ch, *cb);
                        (*cb).lits[0] = (*ch).lit[0];
                    }
                    return true;
                    // panic!("too short clause {} {:#} {:#}", cid2fmt(cid), *ch, *cb);
                }
                let new_lit = (*cb).lits[bi];
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
                if (*cb).lits.len() == 1 {
                    if (*ch).lit[1] == new_lit {
                        panic!("aa");
                        (*ch).lit.swap(0, 1);
                        (*ch).next_watcher.swap(0, 1);
                    }
                    true
                } else {
                    false
                }
            } else {
                debug_assert!((*ch).lit[0] != p.negate() && (*ch).lit[1] != p.negate());
                (*cb).lits.retain(|&x| x != p);
                false
            }
            //             // old code
            //             debug_assert!(1 < (*cb).lits.len());
            //             (*cb).lits.retain(|&x| x != p);
            //             if (*cb).lits.len() == 1 {
            //                 println!("strengthen make a clause {} unit", cid2fmt(cid));
            //                 if (*ch).lit[0] == p {
            //                     (*ch).lit.swap(0, 1);
            //                     (*ch).next_watcher.swap(0, 1);
            //                 }
            //                 let v = &mut self.vars[(*ch).lit[1].vi()];
            //                 assert_eq!(p.vi(), v.index);
            //                 assert_eq!((*ch).lit[1], p);
            //                 assert_ne!((*cb).lits[0], p);
            //                 return true;
            //             }
            //             if (*ch).lit[0] != p && (*ch).lit[1] != p {
            //                 return false;
            //             }
            //             assert!(2 <= (*cb).lits.len());
            //             debug_assert!((*ch).lit[0] == p || (*ch).lit[1] == p);
            //             new_watcher = (*cb).lits[(*cb).lits.len()-1];
            //             assert_ne!(p, new_watcher);
            //             update = (*ch).lit[0] != p;
            //             debug_assert!((*ch).lit[update as usize] == p);
            //             next = (*ch).next_watcher[update as usize];
            //             (*ch).lit[update as usize] = new_watcher;
            //             (*ch).next_watcher[update as usize] = watcher[new_watcher.negate() as usize];
            //             watcher[new_watcher.negate() as usize] = cix;
            //             cj = &mut watcher[p.negate() as usize];
            //             while *cj != NULL_CLAUSE {
            //                 if *cj == cix {
            //                     *cj = next;
            //                     break;
            //                 }
            //                 let h = &mut head[*cj] as *mut ClauseHead;
            //                 debug_assert!((*h).lit[0] == p || (*h).lit[1] == p);
            //                 cj = &mut (*h).next_watcher[((*h).lit[0] != p) as usize];
            //             }
            //         }
            //         false
        }
    }
}

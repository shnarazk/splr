use crate::assign::AssignStack;
use crate::clause::*;
use crate::solver::{propagate_0, SolverConfiguration};
use crate::types::*;
use crate::var::{Var, VarManagement};
// use std::fmt;

/// For Eliminator
pub trait EliminatorIF {
    fn new(use_elim: bool) -> Eliminator;
    fn enqueue_clause(&mut self, cid: ClauseId, ch: &mut ClauseHead) -> ();
    fn enqueue_var(&mut self, v: &mut Var) -> ();
    fn clause_queue_len(&self) -> usize;
    fn var_queue_len(&self) -> usize;
    fn backward_subsumption_check(
        &mut self,
        asgs: &mut AssignStack,
        cp: &mut [ClausePartition],
        stat: &mut [i64],
        vars: &mut [Var],
        ok: &mut bool,
    ) -> bool;
    fn eliminate(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut SolverConfiguration,
        cp: &mut [ClausePartition],
        stat: &mut [i64],
        vars: &mut [Var],
        ok: &mut bool,
    );
    fn extend_model(&mut self, model: &mut Vec<i32>);
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
    fn new(use_elim: bool) -> Eliminator {
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
    fn enqueue_clause(&mut self, cid: ClauseId, ch: &mut ClauseHead) {
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
                ch.flag_on(ClauseFlag::Enqueued);
                self.clause_queue_threshold -= 1;
            }
        }
    }
    fn enqueue_var(&mut self, v: &mut Var) {
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
    /// 10. backwardSubsumptionCheck
    /// returns false if solver is inconsistent
    /// - calls `clause_queue.pop`
    fn backward_subsumption_check(
        &mut self,
        asgs: &mut AssignStack,
        cp: &mut [ClausePartition],
        stat: &mut [i64],
        vars: &mut [Var],
        ok: &mut bool,
    ) -> bool {
        // let Eliminator {
        //     ..
        // } = self;
        let mut cnt = 0;
        let mut _subsumed = 0;
        let mut _deleted_literals = 0;
        debug_assert_eq!(asgs.level(), 0);
        while !self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len() {
            // Empty subsumption queue and return immediately on user-interrupt:
            // if computed-too-long { break; }
            // Check top-level assigments by creating a dummy clause and placing it in the queue:
            if self.clause_queue.is_empty() && self.bwdsub_assigns < asgs.len() {
                let c = asgs.trail[self.bwdsub_assigns].as_uniclause();
                self.clause_queue.push(c);
                self.bwdsub_assigns += 1;
            }
            let cid = self.clause_queue[0];
            self.clause_queue.remove(0);
            unsafe {
                let mut best = 0;
                let unilits: [Lit; 1];
                let lits: &[Lit];
                // let ch = clause_head_mut!(self.cp, cid) as *mut ClauseHead;
                if cid.to_kind() == ClauseKind::Uniclause as usize {
                    best = (cid.to_index() as Lit).vi();
                    unilits = [cid.to_index() as Lit; 1];
                    lits = &unilits;
                } else {
                    let ch = clause_mut!(*cp, cid) as *mut ClauseHead;
                    (*ch).flag_off(ClauseFlag::Enqueued);
                    lits = &(*ch).lits;
                    if (*ch).get_flag(ClauseFlag::Dead) || BACKWORD_SUBSUMPTION_THRESHOLD < cnt {
                        continue;
                    }
                    let mut tmp = 1_000_000;
                    for l in &(*ch).lits {
                        let v = &vars[l.vi()];
                        let nsum = v.pos_occurs.len().min(v.neg_occurs.len());
                        if !v.eliminated && 0 < v.level && nsum < tmp {
                            best = l.vi();
                            tmp = nsum;
                        }
                    }
                }
                if best == 0 || vars[best].eliminated {
                    continue;
                }
                for p in 0..2 {
                    let cs = if p == 0 {
                        &mut vars[best].pos_occurs as *mut Vec<ClauseId>
                    } else {
                        &mut vars[best].neg_occurs as *mut Vec<ClauseId>
                    };
                    cnt += (*cs).len();
                    for di in &*cs {
                        let db = clause!(*cp, di) as *const ClauseHead;
                        if !(*db).get_flag(ClauseFlag::Dead)
                            && *di != cid
                            && lits.len() <= SUBSUMPTION_SIZE
                            && (*db).lits.len() <= SUBSUMPTION_SIZE
                            && (self.subsumption_lim == 0
                                || lits.len() + (*db).lits.len() <= self.subsumption_lim)
                        {
                            match subsume(cp, cid, *di) {
                                Some(NULL_LIT) => {
                                    _subsumed += 1;
                                    if cid.to_kind() == ClauseKind::Removable as usize
                                        && di.to_kind() == ClauseKind::Removable as usize
                                    {
                                        // println!("BackSubsC    => {} {:#} subsumed completely by {} {:#}",
                                        //          cid2fmt(*di),
                                        //          *db,
                                        //          cid2fmt(cid),
                                        //          *clause_body!(self.cp, cid),
                                        // );
                                        cp.remove_clause(*di);
                                        vars.detach_clause(*di, clause!(*cp, *di), self);
                                    } //else {
                                      // println!("backward_subsumption_check tries to delete a permanent clause {} {:#}",
                                      //          cid2fmt(*di),
                                      //          clause_body!(self.cp, *di));
                                      // TODO: move the cid to Permanent
                                      //}
                                }
                                Some(l) => {
                                    cp[di.to_kind()].touched[l as usize] = true;
                                    cp[di.to_kind()].touched[l.negate() as usize] = true;
                                    // let xb = &clause_body!(self.cp, *di);
                                    // println!("BackSubsC    => subsumed {} from {} and {} {:#}", l.int(), cid2fmt(cid), cid2fmt(*di), xb);
                                    _deleted_literals += 1;
                                    // println!("cancel true path");
                                    // continue;
                                    if !strengthen_clause(
                                        cp,
                                        self,
                                        stat,
                                        vars,
                                        asgs,
                                        *di,
                                        l.negate(),
                                    ) {
                                        *ok = false;
                                        return false;
                                    }
                                    self.enqueue_var(&mut vars[l.vi()]);
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

    /// 18. eliminate
    // should be called at decision level 0.
    fn eliminate(
        &mut self,
        asgs: &mut AssignStack,
        config: &mut SolverConfiguration,
        cp: &mut [ClausePartition],
        stat: &mut [i64],
        vars: &mut [Var],
        ok: &mut bool,
    ) {
        if !self.use_elim {
            return;
        }
        if self.next_invocation < self.var_queue.len() {
            self.clause_queue.clear();
            for v in &self.var_queue {
                vars[*v].enqueued = false;
            }
            self.var_queue.clear();
            return;
        }
        // self.next_invocation += 2;
        // println!("eliminate: clause_queue {}", self.clause_queue.len());
        // println!("clause_queue {:?}", self.clause_queue);
        // println!("var_queue {:?}", self.var_queue);
        // println!("n_touched {}", self.n_touched);
        // self.build_occurence_list();
        // for i in 1..4 { println!("eliminate report: v{} => {},{}", i, vars[i].num_occurs, vars[i].occurs.len()); }
        // self.clause_queue.clear();
        'perform: while self.bwdsub_assigns < asgs.len()
            || !self.var_queue.is_empty()
            || !self.clause_queue.is_empty()
        {
            // self.gather_touched_clauses();
            if (!self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len())
                && !self.backward_subsumption_check(asgs, cp, stat, vars, ok)
            {
                *ok = false;
                break 'perform;
            }
            while !self.var_queue.is_empty() {
                let elim = self.var_queue.remove(0);
                vars[elim].enqueued = false;
                if vars[elim].eliminated || vars[elim].assign != BOTTOM {
                    continue;
                }
                // FIXME!
                if !eliminate_var(asgs, config, cp, self, stat, vars, ok, elim) {
                    *ok = false;
                    break 'perform;
                }
            }
        }
        self.clause_queue_threshold = CLAUSE_QUEUE_THRESHOD;
        self.var_queue_threshold = VAR_QUEUE_THRESHOLD;
    }
    /// 17. extendModel
    /// ```c
    /// inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
    /// inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
    /// ```
    fn extend_model(&mut self, model: &mut Vec<i32>) {
        // println!("extend_model {:?}", &self.elim_clauses);
        if self.elim_clauses.is_empty() {
            return;
        }
        let mut i = self.elim_clauses.len() - 1;
        let mut width;
        'next: loop {
            width = self.elim_clauses[i] as usize;
            if width == 0 && i == 0 {
                break;
            }
            i -= 1;
            loop {
                if width <= 1 {
                    break;
                }
                let l = self.elim_clauses[i];
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
            let l = self.elim_clauses[i];
            // debug_assert!(model[l.vi() - 1] != l.negate().int());
            model[l.vi() - 1] = l.int(); // .neg();
            if i < width {
                break;
            }
            i -= width;
        }
    }
}

// impl fmt::Display for Eliminator {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(
//             f,
//             " - n_touched {}\n - clause_queue {:?}\n - heap {:?}",
//             self.n_touched, self.clause_queue, self.var_queue,
//         )
//     }
// }

/// returns a literal if these clauses can be merged by the literal.
fn subsume(cp: &mut [ClausePartition], cid: ClauseId, other: ClauseId) -> Option<Lit> {
    debug_assert!(other.to_kind() != ClauseKind::Uniclause as usize);
    // if other.to_kind() == ClauseKind::Uniclause as usize {
    //     panic!("unexpected path!");
    // }
    if cid.to_kind() == ClauseKind::Uniclause as usize {
        let l = cid.to_index() as Lit;
        let oh = clause!(*cp, other);
        for lo in &oh.lits {
            if l == lo.negate() {
                return Some(l);
            }
        }
        return None;
    }
    // println!("subsume {} = {}:{}", cid, cid.to_kind(), cid.to_index());
    let mut ret: Lit = NULL_LIT;
    let ch = clause!(*cp, cid);
    let ob = clause!(*cp, other);
    debug_assert!(ob.lits.contains(&clause!(*cp, other).lit[0]));
    debug_assert!(ob.lits.contains(&clause!(*cp, other).lit[1]));
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
pub fn strengthen(cp: &mut [ClausePartition], vars: &mut [Var], cid: ClauseId, p: Lit) -> bool {
    debug_assert!(!clause!(cp, cid).get_flag(ClauseFlag::Dead));
    debug_assert!(1 < clause!(cp, cid).lits.len());
    let cix = cid.to_index();
    let ClausePartition {
        ref mut head,
        ref mut watcher,
        ..
    } = cp[cid.to_kind()];
    unsafe {
        let ch = &mut head[cix] as *mut ClauseHead;
        // debug_assert!((*ch).lits.contains(&p));
        // debug_assert!(1 < (*ch).lits.len());
        let v = &mut vars[p.vi()];
        if p.positive() {
            // debug_assert!(v.pos_occurs.contains(&cid));
            v.pos_occurs.retain(|&c| c != cid);
        } else {
            // debug_assert!(v.neg_occurs.contains(&cid));
            v.neg_occurs.retain(|&c| c != cid);
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
            (*ch).lit[hi] = new_lit;
            (*ch).next_watcher[hi] = watcher[new_lit.negate() as usize];
            watcher[new_lit.negate() as usize] = cix;
            debug_assert!((*ch).lits.len() != 1 || (*ch).lit[1] != new_lit);
            (*ch).lits.len() == 1
        } else {
            debug_assert!((*ch).lit[0] != p.negate() && (*ch).lit[1] != p.negate());
            (*ch).lits.retain(|&x| x != p);
            false
        }
    }
}

/// Returns **false** if one of the clauses is always satisfied.
pub fn check_to_merge(
    cpack: &[ClausePartition],
    cp: ClauseId,
    cq: ClauseId,
    v: VarId,
) -> (bool, usize) {
    let pqb = clause!(cpack, cp);
    let qpb = clause!(cpack, cq);
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

/// 13. mkElimClause(1)
fn make_eliminating_unit_clause(vec: &mut Vec<Lit>, x: Lit) {
    vec.push(x);
    vec.push(1);
}

pub fn check_eliminator(cp: &[ClausePartition], vars: &[Var]) -> bool {
    // clause_queue should be clear.
    // debug_assert!(self.eliminator.clause_queue.is_empty());
    // all elements in occur_lists exist.
    for v in vars {
        for c in &v.pos_occurs {
            let ch = clause!(cp, c);
            if ch.lit[0] <= GARBAGE_LIT || ch.lit[1] <= GARBAGE_LIT {
                panic!("panic {:#}", ch);
            }
        }
        for c in &v.neg_occurs {
            let ch = clause!(cp, c);
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
        for (ci, ch) in cp[*kind as usize].head.iter().enumerate().skip(1) {
            let cid = kind.id_from(ci);
            if ch.lit[0] == RECYCLE_LIT && ch.lit[1] == RECYCLE_LIT {
                continue;
            }
            for l in &ch.lits {
                let v = l.vi();
                if l.positive() {
                    if !vars[v].pos_occurs.contains(&cid) {
                        panic!("aaa {} {:#}", cid2fmt(cid), ch);
                    }
                } else if !vars[v].neg_occurs.contains(&cid) {
                    panic!("aaa {} {:#}", cid2fmt(cid), ch);
                }
            }
        }
    }
    true
}

/// 6. merge(1)
/// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
pub fn merge(
    cp: &mut [ClausePartition],
    eliminator: &mut Eliminator,
    cip: ClauseId,
    ciq: ClauseId,
    v: VarId,
) -> Option<Vec<Lit>> {
    let mut vec: Vec<Lit> = Vec::new();
    eliminator.merges += 1;
    let pqb = clause!(*cp, cip);
    let qpb = clause!(*cp, ciq);
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

/// 5. strengthenClause
/// returns false if inconsistent
/// - calls `enqueue_clause`
/// - calls `enqueue_var`
pub fn strengthen_clause(
    cp: &mut [ClausePartition],
    eliminator: &mut Eliminator,
    stat: &mut [i64],
    vars: &mut [Var],
    asgs: &mut AssignStack,
    cid: ClauseId,
    l: Lit,
) -> bool {
    debug_assert!(!clause!(*cp, cid).get_flag(ClauseFlag::Dead));
    debug_assert!(1 < clause!(*cp, cid).lits.len());
    cp[cid.to_kind()].touched[l as usize] = true;
    cp[cid.to_kind()].touched[l.negate() as usize] = true;
    // println!("STRENGTHEN_CLAUSE {}", cid2fmt(cid));
    debug_assert_ne!(cid, NULL_CLAUSE);
    if strengthen(cp, vars, cid, l) {
        // since changing a literal in `lit` requires updating a next_watcher,
        // it's muth easier to hold the literal to be propagated in body.lits[0]
        // let c0 = clause_head!(self.cp, cid).lit[0];
        let c0 = clause!(*cp, cid).lits[0];
        debug_assert!(1 == clause!(*cp, cid).lits.len());
        debug_assert!(c0 == clause!(*cp, cid).lits[0]);
        // println!("cid {} {:?} became a unit clause as c0 {}, l {}", cid2fmt(cid), vec2int(&clause_body!(*cp, cid).lits), c0.int(), l.int());
        debug_assert_ne!(c0, l);
        // println!("{} is removed and its first literal {} is enqueued.", cid2fmt(cid), c0.int());
        cp.remove_clause(cid);
        vars.detach_clause(cid, clause!(*cp, cid), eliminator);
        if asgs.enqueue_null(&mut vars[c0.vi()], c0.lbool(), 0)
            && propagate_0(cp, stat, vars, asgs) == NULL_CLAUSE
        {
            cp[cid.to_kind()].touched[c0.negate() as usize] = true;
            true
        } else {
            false
        }
    } else {
        // println!("cid {} drops literal {}", cid2fmt(cid), l.int());
        debug_assert!(1 < clause!(*cp, cid).lits.len());
        eliminator.enqueue_clause(cid, clause_mut!(*cp, cid));
        true
    }
}

/// 14. mkElimClause(2)
pub fn make_eliminated_clause(
    cp: &mut [ClausePartition],
    vec: &mut Vec<Lit>,
    vi: VarId,
    cid: ClauseId,
) {
    let first = vec.len();
    // Copy clause to the vector. Remember the position where the varibale 'v' occurs:
    let ch = clause!(cp, cid);
    debug_assert!(!ch.lits.is_empty());
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
pub fn eliminate_var(
    asgs: &mut AssignStack,
    config: &mut SolverConfiguration,
    cp: &mut [ClausePartition],
    eliminator: &mut Eliminator,
    stat: &mut [i64],
    vars: &mut [Var],
    ok: &mut bool,
    v: VarId,
) -> bool {
    if vars[v].assign != BOTTOM {
        return true;
    }
    debug_assert!(!vars[v].eliminated);
    {
        // count only alive clauses
        vars[v]
            .pos_occurs
            .retain(|&c| !clause!(cp, c).get_flag(ClauseFlag::Dead));
        vars[v]
            .pos_occurs
            .retain(|&c| !clause!(cp, c).get_flag(ClauseFlag::Dead));
    }
    let pos = &vars[v].pos_occurs as *const Vec<ClauseId>;
    let neg = &vars[v].neg_occurs as *const Vec<ClauseId>;
    unsafe {
        // Check wether the increase in number of clauses stays within the allowed ('grow').
        // Moreover, no clause must exceed the limit on the maximal clause size (if it is set).
        if (*pos).is_empty() && (*neg).is_empty() {
            return true;
        }
        if (*pos).is_empty() && !(*neg).is_empty() {
            // println!("-v {} p {} n {}", v, (*pos).len(), (*neg).len());
            if !asgs.enqueue_null(&mut vars[v], LFALSE, 0)
                || propagate_0(cp, stat, vars, asgs) != NULL_CLAUSE
            {
                *ok = false;
                return false;
            }
            return true;
        }
        if (*neg).is_empty() && (*pos).is_empty() {
            // println!("+v {} p {} n {}", v, (*pos).len(), (*neg).len());
            if !asgs.enqueue_null(&mut vars[v], LTRUE, 0)
                || propagate_0(cp, stat, vars, asgs) != NULL_CLAUSE
            {
                *ok = false;
                // panic!("eliminate_var: failed to enqueue & propagate");
                return false;
            }
            return true;
        }
        let clslen = (*pos).len() + (*neg).len();
        let mut cnt = 0;
        for lit_pos in &*pos {
            if clause!(*cp, lit_pos).get_flag(ClauseFlag::Dead) {
                continue;
            }
            for lit_neg in &*neg {
                if clause!(*cp, lit_neg).get_flag(ClauseFlag::Dead) {
                    continue;
                }
                let (res, clause_size) = check_to_merge(cp, *lit_pos, *lit_neg, v);
                if res {
                    cnt += 1;
                    if clslen + SUBSUMPITON_GROW_LIMIT < cnt
                        || (eliminator.clause_lim != 0 && eliminator.clause_lim < clause_size)
                    {
                        return true;
                    }
                }
            }
        }
        // eliminate the literal and build constraints on it.
        debug_assert!(!vars[v].eliminated);
        vars[v].eliminated = true;
        let cid = vars[v].reason;
        debug_assert_eq!(cid, NULL_CLAUSE);
        // println!("- eliminate var: {:>8} (+{:<4} -{:<4}); {:?}", v, (*pos).len(), (*neg).len(), vars[v]);
        // setDecisionVar(v, false);
        eliminator.eliminated_vars += 1;
        {
            let tmp = &mut eliminator.elim_clauses as *mut Vec<Lit>;
            if (*neg).len() < (*pos).len() {
                for cid in &*neg {
                    if clause!(*cp, cid).get_flag(ClauseFlag::Dead) {
                        continue;
                    }
                    make_eliminated_clause(cp, &mut (*tmp), v, *cid);
                    cp[cid.to_kind() as usize].touched[v.lit(LTRUE) as usize] = true;
                    cp[cid.to_kind() as usize].touched[v.lit(LFALSE) as usize] = true;
                }
                make_eliminating_unit_clause(&mut (*tmp), v.lit(LTRUE));
            // println!("eliminate unit clause {}", v.lit(LFALSE).int());
            } else {
                for cid in &*pos {
                    if clause!(*cp, cid).get_flag(ClauseFlag::Dead) {
                        continue;
                    }
                    make_eliminated_clause(cp, &mut (*tmp), v, *cid);
                    cp[cid.to_kind() as usize].touched[v.lit(LTRUE) as usize] = true;
                    cp[cid.to_kind() as usize].touched[v.lit(LFALSE) as usize] = true;
                }
                make_eliminating_unit_clause(&mut (*tmp), v.lit(LFALSE));
                // println!("eliminate unit clause {}", v.lit(LTRUE).int());
            }
        }
        // Produce clauses in cross product:
        {
            for p in &*pos {
                if clause!(*cp, p).get_flag(ClauseFlag::Dead) {
                    continue;
                }
                let act_p = clause!(*cp, p).activity;
                let rank_p = clause!(*cp, p).rank;
                for n in &*neg {
                    if clause!(*cp, n).get_flag(ClauseFlag::Dead) {
                        continue;
                    }
                    if let Some(vec) = merge(cp, eliminator, *p, *n, v) {
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
                                //     vec2int(&clause_body!(*cp, *p).lits),
                                //     cid2fmt(*n),
                                //     vec2int(&clause_body!(*cp, *n).lits)
                                // );
                                let lit = vec[0];
                                if !asgs.enqueue_null(&mut vars[lit.vi()], lit.lbool(), 0) {
                                    *ok = false;
                                    // panic!("eliminate_var: failed to enqueue & propagate");
                                    return false;
                                }
                            }
                            _ => {
                                if p.to_kind() == ClauseKind::Removable as usize
                                    && n.to_kind() == ClauseKind::Removable as usize
                                {
                                    let act_n = clause!(*cp, n).activity;
                                    let rank_n = clause!(*cp, n).rank;
                                    let new = cp.add_clause(
                                        config,
                                        eliminator,
                                        vars,
                                        &mut vec.to_vec(),
                                        rank_p.min(rank_n),
                                        act_p.max(act_n),
                                    );
                                    clause_mut!(*cp, new).activity = act_p.max(act_n);
                                } else {
                                    cp.add_clause(
                                        config,
                                        eliminator,
                                        vars,
                                        &mut vec.to_vec(),
                                        0,
                                        0.0,
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        for i in 0..2 {
            for cid in if i == 0 {
                &mut vars[v].pos_occurs
            } else {
                &mut vars[v].neg_occurs
            } {
                clause_mut!(*cp, *cid).flag_on(ClauseFlag::Dead);
                let w0;
                let w1;
                {
                    let ch = clause!(*cp, *cid);
                    w0 = ch.lit[0].negate();
                    w1 = ch.lit[1].negate();
                }
                debug_assert!(w0 != 0 && w1 != 0);
                cp[cid.to_kind()].touched[w0 as usize] = true;
                cp[cid.to_kind()].touched[w1 as usize] = true;
            }
            // cp[cid.to_kind()].touched[v.lit(LTRUE) as usize] = true;
            // cp[cid.to_kind()].touched[v.lit(LFALSE) as usize] = true;
        }
        vars[v].pos_occurs.clear();
        vars[v].neg_occurs.clear();
        if propagate_0(cp, stat, vars, asgs) != NULL_CLAUSE {
            *ok = false;
            return false;
        }
        eliminator.backward_subsumption_check(asgs, cp, stat, vars, ok)
    }
}

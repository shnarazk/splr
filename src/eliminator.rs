use crate::clause::{Clause, ClauseDB};
use crate::config::Config;
use crate::propagator::AssignStack;
use crate::state::State;
use crate::traits::*;
use crate::types::*;
use crate::var::Var;
use std::fmt;

/// Literal eliminator
pub struct Eliminator {
    // to make occur lists
    pub in_use: bool,
    // to run eliminate
    pub active: bool,
    clause_queue: Vec<ClauseId>,
    var_queue: VarOccHeap,
    bwdsub_assigns: usize,
    elim_clauses: Vec<Lit>,
}

impl Default for Eliminator {
    fn default() -> Eliminator {
        Eliminator {
            in_use: true,
            active: true,
            var_queue: VarOccHeap::new(0, 0),
            clause_queue: Vec::new(),
            bwdsub_assigns: 0,
            elim_clauses: Vec::new(),
        }
    }
}

impl EliminatorIF for Eliminator {
    fn new(in_use: bool, nv: usize) -> Eliminator {
        let mut e = Eliminator::default();
        e.var_queue = VarOccHeap::new(nv, 0);
        e.in_use = in_use;
        e
    }
    /// FIXME: due to a potential bug of killing clauses and difficulty about
    /// synchronization between 'garbage_collect' and clearing occur lists,
    /// 'stop' should purge all occur lists to purge any dead clauses for now.
    fn stop(&mut self, cdb: &mut ClauseDB, vars: &mut [Var]) {
        let force: bool = true;
        self.clear_clause_queue(cdb);
        self.clear_var_queue(vars);
        if force {
            for c in &mut cdb.clause[1..] {
                c.turn_off(Flag::OccurLinked);
            }
            for v in &mut vars[1..] {
                v.pos_occurs.clear();
                v.neg_occurs.clear();
            }
        }
        self.active = false;
    }
    fn activate(&mut self, cdb: &mut ClauseDB, vars: &mut [Var], force: bool) {
        self.active = true;
        for v in &mut vars[1..] {
            v.pos_occurs.clear();
            v.neg_occurs.clear();
        }
        for (cid, c) in &mut cdb.clause.iter_mut().enumerate().skip(1) {
            if c.is(Flag::DeadClause) || c.is(Flag::OccurLinked) {
                continue;
            }
            self.add_cid_occur(vars, cid, c, false);
        }
        if force {
            for vi in 1..vars.len() {
                let v = &vars[vi];
                if v.is(Flag::EliminatedVar) || v.assign != BOTTOM {
                    continue;
                }
                self.enqueue_var(vars, vi, true);
            }
        }
    }
    #[inline]
    fn enqueue_clause(&mut self, cid: ClauseId, c: &mut Clause) {
        if !self.in_use || !self.active || c.is(Flag::Enqueued) {
            return;
        }
        self.clause_queue.push(cid);
        c.turn_on(Flag::Enqueued);
    }
    fn clear_clause_queue(&mut self, cdb: &mut ClauseDB) {
        for cid in &self.clause_queue {
            cdb.clause[*cid].turn_off(Flag::Enqueued);
        }
        self.clause_queue.clear();
    }
    #[inline]
    fn enqueue_var(&mut self, vars: &mut [Var], vi: VarId, upward: bool) {
        if !self.in_use || !self.active {
            return;
        }
        self.var_queue.insert(vars, vi, upward);
        vars[vi].turn_on(Flag::Enqueued);
    }
    fn clear_var_queue(&mut self, vars: &mut [Var]) {
        self.var_queue.clear(vars);
    }
    fn clause_queue_len(&self) -> usize {
        self.clause_queue.len()
    }
    fn var_queue_len(&self) -> usize {
        self.var_queue.len()
    }
    fn eliminate(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        config: &mut Config,
        state: &mut State,
        vars: &mut [Var],
    ) -> MaybeInconsistent {
        debug_assert!(asgs.level() == 0);
        if !self.in_use || !self.active {
            return Ok(());
        }
        let mut cnt = 0;
        'perform: while self.bwdsub_assigns < asgs.len()
            || !self.var_queue.is_empty()
            || !self.clause_queue.is_empty()
        {
            if !self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len() {
                self.backward_subsumption_check(asgs, cdb, config, vars)?;
            }
            while let Some(vi) = self.var_queue.select_var(vars) {
                let v = &mut vars[vi];
                v.turn_off(Flag::Enqueued);
                cnt += 1;
                if cnt < config.elim_eliminate_loop_limit
                    && !v.is(Flag::EliminatedVar)
                    && v.assign == BOTTOM
                {
                    eliminate_var(asgs, config, cdb, self, state, vars, vi)?;
                }
            }
            self.backward_subsumption_check(asgs, cdb, config, vars)?;
            debug_assert!(self.clause_queue.is_empty());
            cdb.garbage_collect();
            if asgs.propagate(cdb, state, vars) != NULL_CLAUSE {
                return Err(SolverError::Inconsistent);
            }
        }
        Ok(())
    }
    fn extend_model(&mut self, model: &mut Vec<i32>) {
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
                    x if x == l.int() => TRUE,
                    x if -x == l.int() => FALSE,
                    _ => BOTTOM,
                };
                if model_value != FALSE {
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
    fn add_cid_occur(&mut self, vars: &mut [Var], cid: ClauseId, c: &mut Clause, enqueue: bool) {
        if !self.in_use {
            return;
        }
        for l in &c.lits {
            let v = &mut vars[l.vi()];
            v.turn_on(Flag::TouchedVar);
            if !v.is(Flag::EliminatedVar) {
                if l.positive() {
                    debug_assert!(!v.neg_occurs.contains(&cid));
                    v.pos_occurs.push(cid);
                } else {
                    debug_assert!(!v.neg_occurs.contains(&cid));
                    v.neg_occurs.push(cid);
                }
                self.enqueue_var(vars, l.vi(), false);
            }
        }
        if enqueue {
            self.enqueue_clause(cid, c);
        }
    }
    fn remove_lit_occur(&mut self, vars: &mut [Var], l: Lit, cid: ClauseId) {
        let v = &mut vars[l.vi()];
        if l.positive() {
            debug_assert_eq!(v.pos_occurs.iter().filter(|&c| *c == cid).count(), 1);
            v.pos_occurs.delete_unstable(|&c| c == cid);
            debug_assert!(!v.pos_occurs.contains(&cid));
        } else {
            debug_assert_eq!(v.neg_occurs.iter().filter(|&c| *c == cid).count(), 1);
            v.neg_occurs.delete_unstable(|&c| c == cid);
            debug_assert!(!v.neg_occurs.contains(&cid));
        }
        self.enqueue_var(vars, l.vi(), true);
    }
    fn remove_cid_occur(&mut self, vars: &mut [Var], cid: ClauseId, c: &Clause) {
        debug_assert!(c.is(Flag::DeadClause));
        if self.in_use {
            for l in &c.lits {
                let v = &mut vars[l.vi()];
                if !v.is(Flag::EliminatedVar) && v.assign == BOTTOM {
                    self.remove_lit_occur(vars, *l, cid);
                    self.enqueue_var(vars, l.vi(), true);
                }
            }
        }
    }
}

impl Eliminator {
    /// returns false if solver is inconsistent
    /// - calls `clause_queue.pop`
    fn backward_subsumption_check(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        config: &Config,
        vars: &mut [Var],
    ) -> MaybeInconsistent {
        let mut cnt = 0;
        debug_assert_eq!(asgs.level(), 0);
        while !self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len() {
            // Check top-level assigments by creating a dummy clause and placing it in the queue:
            if self.clause_queue.is_empty() && self.bwdsub_assigns < asgs.len() {
                let c = asgs.trail[self.bwdsub_assigns].to_cid();
                self.clause_queue.push(c);
                self.bwdsub_assigns += 1;
            }
            let cid = match self.clause_queue.pop() {
                Some(x) => x,
                None => 0,
            };
            // assert_ne!(cid, 0);
            cnt += 1;
            if config.elim_subsume_loop_limit < cnt {
                continue;
            }
            let best = if cid.is_lifted_lit() {
                cid.to_lit().vi()
            } else {
                let mut tmp = cdb.count(true);
                let c = &mut cdb.clause[cid];
                c.turn_off(Flag::Enqueued);
                let lits = &c.lits;
                if c.is(Flag::DeadClause) || config.elim_subsume_literal_limit < lits.len() {
                    continue;
                }
                // if c is subsumed by c', both of c and c' are included in the occurs of all literals of c
                // so searching the shortest occurs is most efficient.
                let mut b = 0;
                for l in lits {
                    let v = &vars[l.vi()];
                    if v.assign != BOTTOM {
                        continue;
                    }
                    let nsum = if l.positive() {
                        v.neg_occurs.len()
                    } else {
                        v.pos_occurs.len()
                    };
                    if !v.is(Flag::EliminatedVar) && nsum < tmp {
                        b = l.vi();
                        tmp = nsum;
                    }
                }
                b
            };
            if best == 0 || vars[best].is(Flag::EliminatedVar) {
                continue;
            }
            unsafe {
                for cs in &[
                    &mut vars[best].pos_occurs as *mut Vec<ClauseId>,
                    &mut vars[best].neg_occurs as *mut Vec<ClauseId>,
                ] {
                    for did in &**cs {
                        if *did == cid {
                            continue;
                        }
                        let db = &cdb.clause[*did];
                        if !db.is(Flag::DeadClause)
                            && db.lits.len() <= config.elim_subsume_literal_limit
                        {
                            try_subsume(asgs, cdb, self, vars, cid, *did)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

fn try_subsume(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    vars: &mut [Var],
    cid: ClauseId,
    did: ClauseId,
) -> MaybeInconsistent {
    match subsume(cdb, cid, did) {
        Some(NULL_LIT) => {
            // println!("BackSubsC    => {} {:#} subsumed completely by {} {:#}",
            //          did.fmt(),
            //          *clause!(cdb, cid),
            //          cid.fmt(),
            //          *clause!(cdb, cid),
            // );
            cdb.detach(did);
            elim.remove_cid_occur(vars, did, &cdb.clause[did]);
            if !cdb.clause[did].is(Flag::LearntClause) {
                cdb.clause[cid].turn_off(Flag::LearntClause);
            }
        }
        Some(l) => {
            // println!("BackSubC subsumes {} from {} and {}", l.int(), cid.format(), did.format());
            strengthen_clause(cdb, elim, vars, asgs, did, l.negate())?;
            elim.enqueue_var(vars, l.vi(), true);
        }
        None => {}
    }
    Ok(())
}

/// returns a literal if these clauses can be merged by the literal.
fn subsume(cdb: &mut ClauseDB, cid: ClauseId, other: ClauseId) -> Option<Lit> {
    debug_assert!(!other.is_lifted_lit());
    if cid.is_lifted_lit() {
        let l = cid.to_lit();
        let oh = &cdb.clause[other];
        for lo in &oh.lits {
            if l == lo.negate() {
                return Some(l);
            }
        }
        return None;
    }
    let mut ret: Lit = NULL_LIT;
    let ch = &cdb.clause[cid];
    let ob = &cdb.clause[other];
    debug_assert!(ob.lits.contains(&ob.lits[0]));
    debug_assert!(ob.lits.contains(&ob.lits[1]));
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

/// Returns:
/// - `(false, -)` if one of the clauses is always satisfied.
/// - `(true, n)` if they are mergable to a n-literal clause.
fn check_to_merge(
    cdb: &ClauseDB,
    vars: &[Var],
    cp: ClauseId,
    cq: ClauseId,
    v: VarId,
) -> (bool, usize) {
    let pqb = &cdb.clause[cp];
    let qpb = &cdb.clause[cq];
    let ps_smallest = pqb.lits.len() < qpb.lits.len();
    let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
    let mut size = pb.lits.len() + 1;
    'next_literal: for l in &qb.lits {
        if vars[l.vi()].is(Flag::EliminatedVar) {
            println!("ooo");
            continue;
        }
        if l.vi() != v {
            for j in &pb.lits {
                if vars[j.vi()].is(Flag::EliminatedVar) {
                    println!("ooo");
                    continue;
                }
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

#[allow(dead_code)]
fn check_eliminator(cdb: &ClauseDB, vars: &[Var]) -> bool {
    // clause_queue should be clear.
    // all elements in occur_lists exist.
    // for v in vars {
    //     for ci in &v.pos_occurs {
    //         let c = clause!(cp, ci);
    //         if c.lits[0] < 2 || c.lits[1] < 2 {
    //             panic!("panic {:#}", c);
    //         }
    //     }
    //     for ci in &v.neg_occurs {
    //         let c = clause!(cp, ci);
    //         if c.lits[0] < 2 || c.lits[1] < 2 {
    //             panic!("panic {:#}", c);
    //         }
    //     }
    // }
    // all caulses are registered in corresponding occur_lists
    for (cid, c) in cdb.clause.iter().enumerate().skip(1) {
        if c.is(Flag::DeadClause) {
            continue;
        }
        for l in &c.lits {
            let v = l.vi();
            if l.positive() {
                if !vars[v].pos_occurs.contains(&cid) {
                    panic!("failed to check {} {:#}", cid.format(), c);
                }
            } else if !vars[v].neg_occurs.contains(&cid) {
                panic!("failed to check {} {:#}", cid.format(), c);
            }
        }
    }
    true
}

/// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
fn merge(cdb: &mut ClauseDB, cip: ClauseId, ciq: ClauseId, v: VarId) -> Option<Vec<Lit>> {
    let mut vec: Vec<Lit> = Vec::new();
    let pqb = &cdb.clause[cip];
    let qpb = &cdb.clause[ciq];
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

/// removes `l` from clause `cid`
/// - calls `enqueue_clause`
/// - calls `enqueue_var`
fn strengthen_clause(
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    vars: &mut [Var],
    asgs: &mut AssignStack,
    cid: ClauseId,
    l: Lit,
) -> MaybeInconsistent {
    debug_assert!(!cdb.clause[cid].is(Flag::DeadClause));
    debug_assert!(1 < cdb.clause[cid].lits.len());
    cdb.touched[l as usize] = true;
    cdb.touched[l.negate() as usize] = true;
    debug_assert_ne!(cid, NULL_CLAUSE);
    if strengthen(cdb, cid, l) {
        // Vaporize the binary clause
        debug_assert!(2 == cdb.clause[cid].lits.len());
        let c0 = cdb.clause[cid].lits[0];
        debug_assert_ne!(c0, l);
        // println!("{} is removed and its first literal {} is enqueued.", cid.fmt(), c0.int());
        cdb.detach(cid);
        elim.remove_cid_occur(vars, cid, &cdb.clause[cid]);
        asgs.enqueue(&mut vars[c0.vi()], c0.lbool(), NULL_CLAUSE, 0)
    } else {
        // println!("cid {} drops literal {}", cid.fmt(), l.int());
        debug_assert!(1 < cdb.clause[cid].lits.len());
        elim.enqueue_clause(cid, &mut cdb.clause[cid]);
        elim.remove_lit_occur(vars, l, cid);
        Ok(())
    }
}

/// removes Lit `p` from Clause *self*. This is an O(n) function!
/// returns true if the clause became a unit clause.
/// Called only from strengthen_clause
fn strengthen(cdb: &mut ClauseDB, cid: ClauseId, p: Lit) -> bool {
    debug_assert!(!cdb.clause[cid].is(Flag::DeadClause));
    debug_assert!(1 < cdb.clause[cid].lits.len());
    let ClauseDB {
        ref mut clause,
        ref mut watcher,
        ..
    } = cdb;
    let c = &mut clause[cid];
    // debug_assert!((*ch).lits.contains(&p));
    // debug_assert!(1 < (*ch).lits.len());
    if (*c).is(Flag::DeadClause) {
        return false;
    }
    debug_assert!(1 < p.negate());
    let lits = &mut (*c).lits;
    if lits.len() == 2 {
        if lits[0] == p {
            lits.swap(0, 1);
        }
        debug_assert!(1 < lits[0].negate());
        return true;
    }
    watcher[p.negate() as usize].detach_with(cid);
    if lits[0] == p || lits[1] == p {
        let q = if lits[0] == p {
            lits.swap_remove(0);
            lits[0]
        } else {
            lits.swap_remove(1);
            lits[1]
        };
        debug_assert!(1 < p.negate());
        watcher[q.negate() as usize].attach(q, cid);
    } else {
        lits.delete_unstable(|&x| x == p);
    }
    false
}

fn make_eliminating_unit_clause(vec: &mut Vec<Lit>, x: Lit) {
    vec.push(x);
    vec.push(1);
}

fn make_eliminated_clause(cdb: &mut ClauseDB, vec: &mut Vec<Lit>, vi: VarId, cid: ClauseId) {
    let first = vec.len();
    // Copy clause to the vector. Remember the position where the varibale 'v' occurs:
    let c = &cdb.clause[cid];
    debug_assert!(!c.lits.is_empty());
    for l in &c.lits {
        vec.push(*l as Lit);
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
    vec.push(c.lits.len() as Lit);
    cdb.touched[Lit::from_var(vi, TRUE) as usize] = true;
    cdb.touched[Lit::from_var(vi, FALSE) as usize] = true;
    // println!("make_eliminated_clause: eliminate({}) clause {:?}", vi, vec2int(&ch.lits));
}

#[inline]
fn eliminate_var(
    asgs: &mut AssignStack,
    config: &mut Config,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vars: &mut [Var],
    vi: VarId,
) -> MaybeInconsistent {
    let v = &mut vars[vi];
    if v.assign != BOTTOM {
        return Ok(());
    }
    debug_assert!(!v.is(Flag::EliminatedVar));
    // count only alive clauses
    v.pos_occurs
        .retain(|&c| !cdb.clause[c].is(Flag::DeadClause));
    v.neg_occurs
        .retain(|&c| !cdb.clause[c].is(Flag::DeadClause));
    let pos = &v.pos_occurs as *const Vec<ClauseId>;
    let neg = &v.neg_occurs as *const Vec<ClauseId>;
    unsafe {
        if check_var_elimination_condition(cdb, config, vars, &*pos, &*neg, vi) {
            return Ok(());
        }
        let v = &mut vars[vi];
        // OK, eliminate the literal and build constraints on it.
        v.turn_on(Flag::EliminatedVar);
        let cid = v.reason;
        debug_assert_eq!(cid, NULL_CLAUSE);
        state.num_eliminated_vars += 1;
        make_eliminated_clauses(cdb, elim, vi, &*pos, &*neg);
        // Produce clauses in cross product:
        for p in &*pos {
            let rank_p = cdb.clause[*p].rank;
            for n in &*neg {
                if let Some(vec) = merge(cdb, *p, *n, vi) {
                    // println!("eliminator replaces {} with a cross product {:?}", p.fmt(), vec2int(&vec));
                    debug_assert!(!vec.is_empty());
                    match vec.len() {
                        1 => {
                            // println!(
                            //     "eliminate_var: grounds {} from {}{:?} and {}{:?}",
                            //     vec[0].int(),
                            //     p.fmt(),
                            //     vec2int(&clause!(*cp, *p).lits),
                            //     n.fmt(),
                            //     vec2int(&clause!(*cp, *n).lits)
                            // );
                            let lit = vec[0];
                            asgs.enqueue(&mut vars[lit.vi()], lit.lbool(), NULL_CLAUSE, 0)?;
                        }
                        _ => {
                            let v = &mut vec.to_vec();
                            if cdb.clause[*p].is(Flag::LearntClause)
                                && cdb.clause[*n].is(Flag::LearntClause)
                            {
                                let rank = rank_p.min(cdb.clause[*n].rank);
                                cdb.attach(config, elim, vars, v, rank);
                            } else {
                                cdb.attach(config, elim, vars, v, 0);
                            }
                        }
                    }
                }
            }
        }
        for cid in &*pos {
            cdb.detach(*cid);
        }
        for cid in &*neg {
            cdb.detach(*cid);
        }
        vars[vi].pos_occurs.clear();
        vars[vi].neg_occurs.clear();
        elim.backward_subsumption_check(asgs, cdb, config, vars)
    }
}

/// returns `true` if elimination is impossible.
#[inline]
fn check_var_elimination_condition(
    cdb: &ClauseDB,
    config: &Config,
    vars: &[Var],
    pos: &[ClauseId],
    neg: &[ClauseId],
    v: VarId,
) -> bool {
    let clslen = pos.len() + neg.len();
    let mut cnt = 0;
    for c_pos in pos {
        for c_neg in neg {
            let (res, clause_size) = check_to_merge(cdb, vars, *c_pos, *c_neg, v);
            if res {
                cnt += 1;
                if clslen + config.elim_eliminate_grow_limit < cnt
                    || (config.elim_eliminate_combination_limit != 0
                        && config.elim_eliminate_combination_limit < clause_size)
                {
                    return true;
                }
            }
        }
    }
    false
}

fn make_eliminated_clauses(
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    v: VarId,
    pos: &[ClauseId],
    neg: &[ClauseId],
) {
    let tmp = &mut elim.elim_clauses;
    if neg.len() < pos.len() {
        for cid in neg {
            debug_assert!(!cdb.clause[*cid].is(Flag::DeadClause));
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from_var(v, TRUE));
    } else {
        for cid in pos {
            debug_assert!(!cdb.clause[*cid].is(Flag::DeadClause));
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from_var(v, FALSE));
    }
}

impl Var {
    fn occur_activity(&self) -> usize {
        self.pos_occurs.len().min(self.neg_occurs.len())
    }
}

/// heap of VarOccHeap
/// # Note
/// - both fields has a fixed length. Don't use push and pop.
/// - idxs[0] contains the number of alive elements
///   `indx` is positions. So the unused field 0 can hold the last position as a special case.
pub struct VarOccHeap {
    heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
}

trait VarOrderIF {
    fn new(n: usize, init: usize) -> VarOccHeap;
    fn insert(&mut self, vec: &[Var], vi: VarId, upword: bool);
    fn clear(&mut self, vars: &mut [Var]);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn select_var(&mut self, vars: &[Var]) -> Option<VarId>;
    fn rebuild(&mut self, vars: &[Var]);
}

impl VarOrderIF for VarOccHeap {
    fn new(n: usize, init: usize) -> VarOccHeap {
        let mut heap = Vec::with_capacity(n + 1);
        let mut idxs = Vec::with_capacity(n + 1);
        heap.push(0);
        idxs.push(n);
        for i in 1..=n {
            heap.push(i);
            idxs.push(i);
        }
        idxs[0] = init;
        VarOccHeap { heap, idxs }
    }
    fn insert(&mut self, vars: &[Var], vi: VarId, upward: bool) {
        debug_assert!(vi < self.heap.len());
        if self.contains(vi) {
            let i = self.idxs[vi];
            if upward {
                self.percolate_up(vars, i);
            } else {
                self.percolate_down(vars, i);
            }
            return;
        }
        let i = self.idxs[vi];
        let n = self.idxs[0] + 1;
        let vn = self.heap[n];
        self.heap.swap(i, n);
        self.idxs.swap(vi, vn);
        debug_assert!(n < self.heap.len());
        self.idxs[0] = n;
        self.percolate_up(vars, n);
    }
    fn clear(&mut self, vars: &mut [Var]) {
        for v in &mut self.heap[0..self.idxs[0]] {
            vars[*v].turn_off(Flag::Enqueued);
        }
        self.reset()
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
    fn select_var(&mut self, vars: &[Var]) -> Option<VarId> {
        loop {
            let vi = self.get_root(vars);
            if vi == 0 {
                return None;
            }
            if !vars[vi].is(Flag::EliminatedVar) {
                return Some(vi);
            }
        }
    }
    fn rebuild(&mut self, vars: &[Var]) {
        self.reset();
        for v in &vars[1..] {
            if v.assign == BOTTOM && !v.is(Flag::EliminatedVar) {
                self.insert(vars, v.index, true);
            }
        }
    }
}

impl VarOccHeap {
    #[inline(always)]
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn reset(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    fn get_root(&mut self, vars: &[Var]) -> VarId {
        let s = 1;
        let vs = self.heap[s];
        let n = self.idxs[0];
        debug_assert!(n < self.heap.len());
        if n == 0 {
            return 0;
        }
        let vn = self.heap[n];
        debug_assert!(vn != 0, "Invalid VarId for heap");
        debug_assert!(vs != 0, "Invalid VarId for heap");
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vars, 1);
        }
        vs
    }
    fn percolate_up(&mut self, vars: &[Var], start: usize) {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = vars[vq].occur_activity();
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vars[vp].occur_activity();
                if ap > aq {
                    // move down the current parent, and make it empty
                    self.heap[q] = vp;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vp] = q;
                    q = p;
                } else {
                    self.heap[q] = vq;
                    debug_assert!(vq != 0, "Invalid index in percolate_up");
                    self.idxs[vq] = q;
                    return;
                }
            }
        }
    }
    fn percolate_down(&mut self, vars: &[Var], start: usize) {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i];
        let ai = vars[vi].occur_activity();
        loop {
            let l = 2 * i; // left
            if l < n {
                let vl = self.heap[l];
                let al = vars[vl].occur_activity();
                let r = l + 1; // right
                let (target, vc, ac) = if r < n && al > vars[self.heap[r]].occur_activity() {
                    let vr = self.heap[r];
                    (r, vr, vars[vr].occur_activity())
                } else {
                    (l, vl, al)
                };
                if ai > ac {
                    self.heap[i] = vc;
                    self.idxs[vc] = i;
                    i = target;
                } else {
                    self.heap[i] = vi;
                    debug_assert!(vi != 0, "invalid index");
                    self.idxs[vi] = i;
                    return;
                }
            } else {
                self.heap[i] = vi;
                debug_assert!(vi != 0, "invalid index");
                self.idxs[vi] = i;
                return;
            }
        }
    }
    #[allow(dead_code)]
    fn peek(&self) -> VarId {
        self.heap[1]
    }
    #[allow(dead_code)]
    fn remove(&mut self, vec: &[Var], vs: VarId) {
        let s = self.idxs[vs];
        let n = self.idxs[0];
        if n < s {
            return;
        }
        let vn = self.heap[n];
        self.heap.swap(n, s);
        self.idxs.swap(vn, vs);
        self.idxs[0] -= 1;
        if 1 < self.idxs[0] {
            self.percolate_down(&vec, 1);
        }
    }
    #[allow(dead_code)]
    fn check(&self, s: &str) {
        let h = &mut self.heap.clone()[1..];
        let d = &mut self.idxs.clone()[1..];
        h.sort();
        d.sort();
        for i in 0..h.len() {
            if h[i] != i + 1 {
                panic!("heap {} {} {:?}", i, h[i], h);
            }
            if d[i] != i + 1 {
                panic!("idxs {} {} {:?}", i, d[i], d);
            }
        }
        println!(" - pass var_order test at {}", s);
    }
}

impl fmt::Display for VarOccHeap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            " - seek pointer - nth -> var: {:?}\n - var -> nth: {:?}",
            self.heap, self.idxs,
        )
    }
}

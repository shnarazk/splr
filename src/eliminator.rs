use crate::assign::AssignStack;
use crate::clause::{Clause, ClauseDB};
use crate::config::Config;
use crate::state::State;
use crate::traits::*;
use crate::types::*;
use crate::var::Var;

/// Literal eliminator
pub struct Eliminator {
    // to make occur lists
    pub in_use: bool,
    // to run eliminate
    pub active: bool,
    clause_queue: Vec<ClauseId>,
    pub var_queue: Vec<VarId>,
    bwdsub_assigns: usize,
    elim_clauses: Vec<Lit>,
}

const SUBSUMPTION_SIZE: usize = 30;
const BACKWORD_SUBSUMPTION_THRESHOLD: usize = 400_000;
const ELIMINATE_LOOP_THRESHOLD: usize = 4_000_000;

impl Default for Eliminator {
    fn default() -> Eliminator {
        Eliminator {
            in_use: true,
            active: true,
            var_queue: Vec::new(),
            clause_queue: Vec::new(),
            bwdsub_assigns: 0,
            elim_clauses: Vec::new(),
        }
    }
}

impl EliminatorIF for Eliminator {
    fn new(in_use: bool) -> Eliminator {
        let mut e = Eliminator::default();
        e.in_use = in_use;
        e
    }
    fn stop(&mut self, cdb: &mut ClauseDB, vars: &mut [Var], force: bool) {
        self.clear_clause_queue(cdb);
        self.clear_var_queue(vars);
        if force {
            for v in &mut vars[1..] {
                v.pos_occurs.clear();
                v.neg_occurs.clear();
            }
        }
        self.in_use = false;
        self.active = false;
    }
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
    fn enqueue_var(&mut self, v: &mut Var) {
        if !self.in_use || !self.active {
            return;
        }
        v.sve_activity += 1;
        if v.is(Flag::Enqueued) {
            return;
        }
        self.var_queue.push(v.index);
        v.turn_on(Flag::Enqueued);
    }
    fn clear_var_queue(&mut self, vars: &mut [Var]) {
        for v in &self.var_queue {
            vars[*v].turn_off(Flag::Enqueued);
        }
        self.var_queue.clear();
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
    ) {
        debug_assert!(asgs.level() == 0);
        if !self.in_use || !self.active {
            return;
        }
        let mut cnt = 0;
        self.var_queue.sort_by(|&a, &b| {
            let va = vars[a].sve_activity;
            let vb = vars[b].sve_activity;
            vb.cmp(&va)
        });
        'perform: while self.bwdsub_assigns < asgs.len()
            || !self.var_queue.is_empty()
            || !self.clause_queue.is_empty()
        {
            if (!self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len())
                && !self.backward_subsumption_check(asgs, cdb, config, state, vars)
            {
                state.ok = false;
                break 'perform;
            }
            while let Some(vi) = self.var_queue.pop() {
                let v = &mut vars[vi];
                v.turn_off(Flag::Enqueued);
                cnt += 1;
                if ELIMINATE_LOOP_THRESHOLD <= cnt {
                    continue;
                }
                if v.is(Flag::EliminatedVar) || v.assign != BOTTOM {
                    continue;
                }
                v.sve_activity = 0;
                if !eliminate_var(asgs, config, cdb, self, state, vars, vi) {
                    state.ok = false;
                    return;
                }
            }
        }
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

impl Eliminator {
    /// returns false if solver is inconsistent
    /// - calls `clause_queue.pop`
    fn backward_subsumption_check(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        config: &Config,
        state: &mut State,
        vars: &mut [Var],
    ) -> bool {
        let mut cnt = 0;
        debug_assert_eq!(asgs.level(), 0);
        while !self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len() {
            // Empty subsumption queue and return immediately on user-interrupt:
            // if computed-too-long { break; }
            // Check top-level assigments by creating a dummy clause and placing it in the queue:
            if self.clause_queue.is_empty() && self.bwdsub_assigns < asgs.len() {
                let c = asgs.trail[self.bwdsub_assigns].to_cid();
                self.clause_queue.push(c);
                self.bwdsub_assigns += 1;
            }
            let cid = self.clause_queue[0];
            self.clause_queue.remove(0);
            unsafe {
                let mut best = 0;
                let unilits: [Lit; 1];
                let lits: &[Lit];
                if cid.is_lifted_lit() {
                    best = cid.to_lit().vi();
                    unilits = [cid.to_lit(); 1];
                    lits = &unilits;
                } else {
                    let c = &mut cdb.clause[cid] as *mut Clause;
                    (*c).turn_off(Flag::Enqueued);
                    lits = &(*c).lits;
                    if (*c).is(Flag::DeadClause)
                        || BACKWORD_SUBSUMPTION_THRESHOLD < cnt
                        || SUBSUMPTION_SIZE < lits.len()
                    {
                        continue;
                    }
                    let mut tmp = cdb.count(true);
                    for l in &(*c).lits {
                        let v = &vars[l.vi()];
                        let nsum = v.pos_occurs.len().min(v.neg_occurs.len());
                        if !v.is(Flag::EliminatedVar) && 0 < v.level && nsum < tmp {
                            best = l.vi();
                            tmp = nsum;
                        }
                    }
                }
                if best == 0 || vars[best].is(Flag::EliminatedVar) {
                    continue;
                }
                for p in 0..2 {
                    let cs = if p == 0 {
                        &mut vars[best].pos_occurs as *mut Vec<ClauseId>
                    } else {
                        &mut vars[best].neg_occurs as *mut Vec<ClauseId>
                    };
                    cnt += (*cs).len();
                    for did in &*cs {
                        let db = &cdb.clause[*did] as *const Clause;
                        if !(*db).is(Flag::DeadClause)
                            && *did != cid
                            && (*db).lits.len() <= SUBSUMPTION_SIZE
                            && (config.subsume_combination_limit == 0
                                || lits.len() + (*db).lits.len()
                                    <= config.subsume_combination_limit)
                            && !try_subsume(asgs, cdb, self, state, vars, cid, *did)
                        {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
}

fn try_subsume(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vars: &mut [Var],
    cid: ClauseId,
    did: ClauseId,
) -> bool {
    match subsume(cdb, cid, did) {
        Some(NULL_LIT) => {
            if !cid.is_lifted_lit()
                && cdb.clause[cid].is(Flag::LearntClause)
                && cdb.clause[did].is(Flag::LearntClause)
            {
                // println!("BackSubsC    => {} {:#} subsumed completely by {} {:#}",
                //          did.fmt(),
                //          *clause!(cdb, cid),
                //          cid.fmt(),
                //          *clause!(cdb, cid),
                // );
                cdb.detach(did);
                vars.detach(elim, did, &cdb.clause[did]);
            } //else {
              // println!("BackSubsC deletes a permanent clause {} {:#}",
              //          di.fmt(),
              //          clause!(cdb, did));
              // TODO: move the cid to Permanent
              //}
        }
        Some(l) => {
            // println!("BackSubsC subsumeds{} from {} and {} {:#}", l.int(), cid.fmt(), di.fmt());
            if !strengthen_clause(cdb, elim, state, vars, asgs, did, l.negate()) {
                state.ok = false;
                return false;
            }
            elim.enqueue_var(&mut vars[l.vi()]);
        }
        None => {}
    }
    true
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

/// Returns **false** if one of the clauses is always satisfied.
fn check_to_merge(cdb: &ClauseDB, cp: ClauseId, cq: ClauseId, v: VarId) -> (bool, usize) {
    let pqb = &cdb.clause[cp];
    let qpb = &cdb.clause[cq];
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

/// returns false if inconsistent
/// - calls `enqueue_clause`
/// - calls `enqueue_var`
fn strengthen_clause(
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vars: &mut [Var],
    asgs: &mut AssignStack,
    cid: ClauseId,
    l: Lit,
) -> bool {
    debug_assert!(!cdb.clause[cid].is(Flag::DeadClause));
    debug_assert!(1 < cdb.clause[cid].lits.len());
    cdb.touched[l as usize] = true;
    cdb.touched[l.negate() as usize] = true;
    debug_assert_ne!(cid, NULL_CLAUSE);
    if strengthen(cdb, vars, cid, l) {
        debug_assert!(2 == cdb.clause[cid].lits.len());
        let c0 = cdb.clause[cid].lits[0];
        debug_assert_ne!(c0, l);
        // println!("{} is removed and its first literal {} is enqueued.", cid.fmt(), c0.int());
        cdb.detach(cid);
        vars.detach(elim, cid, &cdb.clause[cid]);
        if asgs.enqueue_null(&mut vars[c0.vi()], c0.lbool(), 0)
            && asgs.propagate(cdb, state, vars) == NULL_CLAUSE
        {
            cdb.touched[c0.negate() as usize] = true;
            true
        } else {
            false
        }
    } else {
        // println!("cid {} drops literal {}", cid.fmt(), l.int());
        debug_assert!(1 < cdb.clause[cid].lits.len());
        elim.enqueue_clause(cid, &mut cdb.clause[cid]);
        true
    }
}

/// removes Lit `p` from Clause *self*. This is an O(n) function!
/// returns true if the clause became a unit clause.
/// Called only from strengthen_clause
fn strengthen(cdb: &mut ClauseDB, vars: &mut [Var], cid: ClauseId, p: Lit) -> bool {
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
    let v = &mut vars[p.vi()];
    if p.positive() {
        // debug_assert!(v.pos_occurs.contains(&cid));
        v.pos_occurs.delete_unstable(|&c| c == cid);
    } else {
        // debug_assert!(v.neg_occurs.contains(&cid));
        v.neg_occurs.delete_unstable(|&c| c == cid);
    }
    if (*c).is(Flag::DeadClause) {
        return false;
    }
    watcher[p.negate() as usize].detach_with(cid);
    let lits = &mut (*c).lits;
    if lits.len() == 2 {
        // remove it
        if lits[0] == p {
            lits.swap(0, 1);
        }
        watcher[lits[0].negate() as usize].detach_with(cid);
        return true;
    }
    if lits[0] == p || lits[1] == p {
        let q = if lits[0] == p {
            lits.swap_remove(0);
            lits[0]
        } else {
            lits.swap_remove(1);
            lits[1]
        };
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
    cdb.touched[Lit::from_var(vi, LTRUE) as usize] = true;
    cdb.touched[Lit::from_var(vi, LFALSE) as usize] = true;
    // println!("make_eliminated_clause: eliminate({}) clause {:?}", vi, vec2int(&ch.lits));
}

/// returns false if solver is in inconsistent
fn eliminate_var(
    asgs: &mut AssignStack,
    config: &mut Config,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vars: &mut [Var],
    vi: VarId,
) -> bool {
    let v = &mut vars[vi];
    if v.assign != BOTTOM {
        return true;
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
        // Check wether the increase in number of clauses stays within the allowed ('grow').
        // Moreover, no clause must exceed the limit on the maximal clause size (if it is set).
        if (*pos).is_empty() && (*neg).is_empty() {
            return true;
        }
        if (*pos).is_empty() && !(*neg).is_empty() {
            // println!("-v {} p {} n {}", v, (*pos).len(), (*neg).len());
            if !asgs.enqueue_null(v, LFALSE, 0) || asgs.propagate(cdb, state, vars) != NULL_CLAUSE {
                state.ok = false;
                return false;
            }
            return true;
        } else if (*neg).is_empty() && (*pos).is_empty() {
            // println!("+v {} p {} n {}", v, (*pos).len(), (*neg).len());
            if !asgs.enqueue_null(v, LTRUE, 0) || asgs.propagate(cdb, state, vars) != NULL_CLAUSE {
                state.ok = false;
                return false;
            }
            return true;
        }
        if check_var_elimination_condition(cdb, config, &*pos, &*neg, vi) {
            return true;
        }
        // OK, eliminate the literal and build constraints on it.
        v.turn_on(Flag::EliminatedVar);
        let cid = v.reason;
        debug_assert_eq!(cid, NULL_CLAUSE);
        // println!("- eliminate var: {:>8} (+{:<4} -{:<4}); {:?}", v, (*pos).len(), (*neg).len(), v);
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
                            if !asgs.enqueue_null(&mut vars[lit.vi()], lit.lbool(), 0) {
                                state.ok = false;
                                return false;
                            }
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
        if asgs.propagate(cdb, state, vars) != NULL_CLAUSE {
            state.ok = false;
            return false;
        }
        elim.backward_subsumption_check(asgs, cdb, config, state, vars)
    }
}

fn check_var_elimination_condition(
    cdb: &ClauseDB,
    config: &Config,
    pos: &[ClauseId],
    neg: &[ClauseId],
    v: VarId,
) -> bool {
    let clslen = pos.len() + neg.len();
    let mut cnt = 0;
    for c_pos in pos {
        for c_neg in neg {
            let (res, clause_size) = check_to_merge(cdb, *c_pos, *c_neg, v);
            if res {
                cnt += 1;
                if clslen + config.subsume_grow_limit < cnt
                    || (config.subsume_literal_limit != 0
                        && config.subsume_literal_limit < clause_size)
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
        make_eliminating_unit_clause(tmp, Lit::from_var(v, LTRUE));
    } else {
        for cid in pos {
            debug_assert!(!cdb.clause[*cid].is(Flag::DeadClause));
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from_var(v, LFALSE));
    }
}

/// Crate `eliminator` implments clause subsumption and var elimination.
use {
    crate::{
        clause::{Clause, ClauseDB, ClauseDBIF, ClauseIF, ClauseId, ClauseIdIF, WatchDBIF},
        config::Config,
        propagator::{AssignStack, PropagatorIF},
        state::{State, StateIF},
        types::*,
        var::{Var, VarDB, VarDBIF},
    },
    std::{fmt, slice::Iter},
    std::{
        sync::{
            atomic::{AtomicBool, Ordering},
            Arc,
        },
        thread,
        time::Duration,
    },
};

/// API for Eliminator like `activate`, `stop`, `eliminate` and so on.
pub trait EliminatorIF {
    /// set eliminator's mode to **ready**.
    fn activate(&mut self);
    /// set eliminator's mode to **dormant**.
    fn stop(&mut self, cdb: &mut ClauseDB, vdb: &mut VarDB);
    /// check if the eliminator is running.
    fn is_running(&self) -> bool;
    /// check if the eliminator is active and waits for next `eliminate`.
    fn is_waiting(&self) -> bool;
    /// rebuild occur lists.
    fn prepare(&mut self, cdb: &mut ClauseDB, vdb: &mut VarDB, force: bool);
    /// enqueue a var into eliminator's var queue.
    fn enqueue_var(&mut self, vdb: &mut VarDB, vi: VarId, upword: bool);
    /// run clause subsumption and variable elimination.
    ///
    /// # Errors
    ///
    /// if solver becomes inconsistent.
    fn eliminate(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        state: &mut State,
        vdb: &mut VarDB,
    ) -> MaybeInconsistent;
    /// inject assignments for eliminated vars.
    fn extend_model(&mut self, vdb: &mut VarDB);
    /// register a clause id to all corresponding occur lists.
    fn add_cid_occur(&mut self, vdb: &mut VarDB, cid: ClauseId, c: &mut Clause, enqueue: bool);
    /// remove a clause id from all corresponding occur lists.
    fn remove_cid_occur(&mut self, vdb: &mut VarDB, cid: ClauseId, c: &mut Clause);
    /// return the order of vars based on their occurrences
    fn sorted_iterator(&self) -> Iter<'_, usize>;
}

#[derive(Eq, Debug, PartialEq)]
enum EliminatorMode {
    Deactive,
    Waiting,
    Running,
}

/// Literal eliminator
#[derive(Debug)]
pub struct Eliminator {
    pub enable: bool,
    mode: EliminatorMode,
    clause_queue: Vec<ClauseId>,
    var_queue: VarOccHeap,
    bwdsub_assigns: usize,
    elim_clauses: Vec<Lit>,
    /// 0 for no limit
    /// Stop elimination if a generated resolvent is larger than this
    /// 0 means no limit.
    pub eliminate_combination_limit: usize,
    /// Stop elimination if the increase of clauses is over this
    pub eliminate_grow_limit: usize,
    /// A criteria by the product's of its positive occurrences and negative ones
    pub eliminate_occurrence_limit: usize,
    /// Stop subsumption if the size of a clause is over this
    pub subsume_literal_limit: usize,
}

impl Default for Eliminator {
    fn default() -> Eliminator {
        Eliminator {
            enable: true,
            mode: EliminatorMode::Deactive,
            var_queue: VarOccHeap::new(0, 0),
            clause_queue: Vec::new(),
            bwdsub_assigns: 0,
            elim_clauses: Vec::new(),
            eliminate_combination_limit: 80,
            eliminate_grow_limit: 0, // 64
            eliminate_occurrence_limit: 800,
            subsume_literal_limit: 100,
        }
    }
}

impl Instantiate for Eliminator {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Eliminator {
        let nv = cnf.num_of_variables;
        let mut e = Eliminator::default();
        e.enable = !config.without_elim;
        e.var_queue = VarOccHeap::new(nv, 0);
        e.eliminate_grow_limit = config.elim_grow_limit;
        e.subsume_literal_limit = config.elim_lit_limit;
        e
    }
}

impl EliminatorIF for Eliminator {
    fn activate(&mut self) {
        debug_assert!(self.mode != EliminatorMode::Running);
        self.mode = EliminatorMode::Waiting;
    }
    fn is_running(&self) -> bool {
        self.mode == EliminatorMode::Running
    }
    fn is_waiting(&self) -> bool {
        self.mode == EliminatorMode::Waiting
    }
    // Due to a potential bug of killing clauses and difficulty about
    // synchronization between 'garbage_collect' and clearing occur lists,
    // 'stop' should purge all occur lists to purge any dead clauses for now.
    fn stop(&mut self, cdb: &mut ClauseDB, vdb: &mut VarDB) {
        let force: bool = true;
        self.clear_clause_queue(cdb);
        self.clear_var_queue(vdb);
        if force {
            for c in &mut cdb[1..] {
                c.turn_off(Flag::OCCUR_LINKED);
            }
            for v in &mut vdb[1..] {
                v.pos_occurs.clear();
                v.neg_occurs.clear();
            }
        }
        self.mode = EliminatorMode::Deactive;
    }
    fn prepare(&mut self, cdb: &mut ClauseDB, vdb: &mut VarDB, force: bool) {
        if self.mode != EliminatorMode::Waiting {
            return;
        }
        self.mode = EliminatorMode::Running;
        for v in &mut vdb[1..] {
            v.pos_occurs.clear();
            v.neg_occurs.clear();
        }
        for (cid, c) in &mut cdb[0..].iter_mut().enumerate().skip(1) {
            if c.is(Flag::DEAD) || c.is(Flag::OCCUR_LINKED) {
                continue;
            }
            self.add_cid_occur(vdb, ClauseId::from(cid), c, false);
        }
        if force {
            for vi in 1..vdb.len() {
                let v = &vdb[vi];
                if v.is(Flag::ELIMINATED) || v.assign.is_some() {
                    continue;
                }
                self.enqueue_var(vdb, vi, true);
            }
        }
    }
    fn enqueue_var(&mut self, vdb: &mut VarDB, vi: VarId, upward: bool) {
        if self.mode != EliminatorMode::Running {
            return;
        }
        let v = &mut vdb[vi];
        if !v.is(Flag::ENQUEUED) && v.occur_activity() < self.eliminate_occurrence_limit {
            v.turn_on(Flag::ENQUEUED);
            self.var_queue.insert(vdb, vi, upward);
        }
    }
    fn eliminate(&mut self,
                 asgs: &mut AssignStack,
                 cdb: &mut ClauseDB,
                 state: &mut State,
                 vdb: &mut VarDB
    ) -> MaybeInconsistent {
        let start = state.elapsed().unwrap_or(0.0);
        loop {
            let na = asgs.len();
            self.eliminate_main(asgs, cdb, state, vdb)?;
            cdb.eliminate_satisfied_clauses(self, vdb, true);
            if na == asgs.len()
                && (!self.is_running()
                    || (0 == self.clause_queue_len() && 0 == self.var_queue_len()))
            {
                break;
            }
            if 0.1 <= state.elapsed().unwrap_or(1.0) - start {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(vdb);
                break;
            }
        }
        Ok(())
    }
    fn extend_model(&mut self, vdb: &mut VarDB) {
        if self.elim_clauses.is_empty() {
            return;
        }
        let mut i = self.elim_clauses.len() - 1;
        let mut width;
        'next: loop {
            width = usize::from(self.elim_clauses[i]);
            if width == 0 && i == 0 {
                break;
            }
            i -= 1;
            loop {
                if width <= 1 {
                    break;
                }
                let l = self.elim_clauses[i];
                // let model_value = match model[l.vi() - 1] {
                //     x if x == l.to_i32() => Some(true),
                //     x if -x == l.to_i32() => Some(false),
                //     _ => None,
                // };
                // if model_value != Some(false) {
                if !Lit::from(&vdb[l]) != l {
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
            vdb[l].assign = Some(bool::from(l));
            if i < width {
                break;
            }
            i -= width;
        }
    }
    fn add_cid_occur(&mut self, vdb: &mut VarDB, cid: ClauseId, c: &mut Clause, enqueue: bool) {
        if self.mode != EliminatorMode::Running || c.is(Flag::OCCUR_LINKED) {
            return;
        }
        for l in &c.lits {
            let v = &mut vdb[l.vi()];
            v.turn_on(Flag::TOUCHED);
            if !v.is(Flag::ELIMINATED) {
                if bool::from(*l) {
                    debug_assert!(
                        !v.pos_occurs.contains(&cid),
                        format!("{} {:?} {}", cid.format(), vec2int(&c.lits), v.index,)
                    );
                    v.pos_occurs.push(cid);
                } else {
                    debug_assert!(
                        !v.neg_occurs.contains(&cid),
                        format!("{} {:?} {}", cid.format(), vec2int(&c.lits), v.index,)
                    );
                    v.neg_occurs.push(cid);
                }
                self.enqueue_var(vdb, l.vi(), false);
            }
        }
        c.turn_on(Flag::OCCUR_LINKED);
        if enqueue {
            self.enqueue_clause(cid, c);
        }
    }
    fn remove_cid_occur(&mut self, vdb: &mut VarDB, cid: ClauseId, c: &mut Clause) {
        debug_assert!(self.mode == EliminatorMode::Running);
        debug_assert!(!cid.is_lifted_lit());
        c.turn_off(Flag::OCCUR_LINKED);
        debug_assert!(c.is(Flag::DEAD));
        for l in &c.lits {
            if vdb[l.vi()].assign.is_none() {
                self.remove_lit_occur(vdb, *l, cid);
                self.enqueue_var(vdb, l.vi(), true);
            }
        }
    }
    fn sorted_iterator(&self) -> Iter<'_, usize> {
        self.var_queue.heap[1..].iter()
    }
}

impl Eliminator {
    /// returns false if solver is inconsistent
    /// - calls `clause_queue.pop`
    fn backward_subsumption_check(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        vdb: &mut VarDB,
        timedout: &Arc<AtomicBool>,
    ) -> MaybeInconsistent {
        debug_assert_eq!(asgs.level(), 0);
        while !self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len() {
            // Check top-level assignments by creating a dummy clause and placing it in the queue:
            if self.clause_queue.is_empty() && self.bwdsub_assigns < asgs.len() {
                let c = ClauseId::from(asgs[self.bwdsub_assigns]);
                self.clause_queue.push(c);
                self.bwdsub_assigns += 1;
            }
            let cid = match self.clause_queue.pop() {
                Some(x) => x,
                None => ClauseId::default(),
            };
            // assert_ne!(cid, 0);
            if timedout.load(Ordering::Acquire) {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(vdb);
                continue;
            }
            let best = if cid.is_lifted_lit() {
                Lit::from(cid).vi()
            } else {
                let mut tmp = cdb.count(true);
                let c = &mut cdb[cid];
                c.turn_off(Flag::ENQUEUED);
                let lits = &c.lits;
                if c.is(Flag::DEAD) || self.subsume_literal_limit < lits.len() {
                    continue;
                }
                // if c is subsumed by c', both of c and c' are included in the occurs of all literals of c
                // so searching the shortest occurs is most efficient.
                let mut b = 0;
                for l in lits {
                    let v = &vdb[l.vi()];
                    if v.assign.is_some() {
                        continue;
                    }
                    let nsum = if bool::from(*l) {
                        v.neg_occurs.len()
                    } else {
                        v.pos_occurs.len()
                    };
                    if !v.is(Flag::ELIMINATED) && nsum < tmp {
                        b = l.vi();
                        tmp = nsum;
                    }
                }
                b
            };
            if best == 0 || vdb[best].is(Flag::ELIMINATED) {
                continue;
            }
            unsafe {
                for cs in &[
                    &mut vdb[best].pos_occurs as *mut Vec<ClauseId>,
                    &mut vdb[best].neg_occurs as *mut Vec<ClauseId>,
                ] {
                    for did in &**cs {
                        if *did == cid {
                            continue;
                        }
                        let db = &cdb[did];
                        if !db.is(Flag::DEAD) && db.len() <= self.subsume_literal_limit {
                            try_subsume(asgs, cdb, self, vdb, cid, *did)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
    /// do the elimination task
    fn eliminate_main(
        &mut self,
        asgs: &mut AssignStack,
        cdb: &mut ClauseDB,
        state: &mut State,
        vdb: &mut VarDB,
    ) -> MaybeInconsistent {
        debug_assert!(asgs.level() == 0);
        if self.mode == EliminatorMode::Deactive {
            return Ok(());
        }
        let timedout = Arc::new(AtomicBool::new(false));
        let timedout2 = timedout.clone();
        let time = 100 * state.config.timeout as u64;
        thread::spawn(move || {
            thread::sleep(Duration::from_millis(time));
            timedout2.store(true, Ordering::Release);
        });
        while self.bwdsub_assigns < asgs.len()
            || !self.var_queue.is_empty()
            || !self.clause_queue.is_empty()
        {
            if !self.clause_queue.is_empty() || self.bwdsub_assigns < asgs.len() {
                self.backward_subsumption_check(asgs, cdb, vdb, &timedout)?;
            }
            while let Some(vi) = self.var_queue.select_var(vdb) {
                // timedout = cvar.wait(timedout).unwrap();
                let v = &mut vdb[vi];
                v.turn_off(Flag::ENQUEUED);
                if !v.is(Flag::ELIMINATED) && v.assign.is_none() {
                    eliminate_var(asgs, cdb, self, state, vdb, vi, &timedout)?;
                }
            }
            self.backward_subsumption_check(asgs, cdb, vdb, &timedout)?;
            debug_assert!(self.clause_queue.is_empty());
            cdb.garbage_collect();
            if asgs.propagate(cdb, vdb) != ClauseId::default() {
                return Err(SolverError::Inconsistent);
            }
            cdb.eliminate_satisfied_clauses(self, vdb, true);
            cdb.garbage_collect();
            if timedout.load(Ordering::Acquire) {
                self.clear_clause_queue(cdb);
                self.clear_var_queue(vdb);
            }
        }
        Ok(())
    }
    /// remove a clause id from literal's occur list.
    fn remove_lit_occur(&mut self, vdb: &mut VarDB, l: Lit, cid: ClauseId) {
        let v = &mut vdb[l.vi()];
        if bool::from(l) {
            debug_assert_eq!(v.pos_occurs.iter().filter(|&c| *c == cid).count(), 1);
            v.pos_occurs.delete_unstable(|&c| c == cid);
            debug_assert!(!v.pos_occurs.contains(&cid));
        } else {
            debug_assert_eq!(v.neg_occurs.iter().filter(|&c| *c == cid).count(), 1);
            v.neg_occurs.delete_unstable(|&c| c == cid);
            debug_assert!(!v.neg_occurs.contains(&cid));
        }
        self.enqueue_var(vdb, l.vi(), true);
    }

    ///
    /// clause queue operations
    ///

    /// enqueue a clause into eliminator's clause queue.
    fn enqueue_clause(&mut self, cid: ClauseId, c: &mut Clause) {
        if self.mode != EliminatorMode::Running || c.is(Flag::ENQUEUED) {
            return;
        }
        self.clause_queue.push(cid);
        c.turn_on(Flag::ENQUEUED);
    }
    /// clear eliminator's clause queue.
    fn clear_clause_queue(&mut self, cdb: &mut ClauseDB) {
        for cid in &self.clause_queue {
            cdb[cid].turn_off(Flag::ENQUEUED);
        }
        self.clause_queue.clear();
    }
    /// return the length of eliminator's clause queue.
    fn clause_queue_len(&self) -> usize {
        self.clause_queue.len()
    }

    ///
    /// var queue operations
    ///

    /// clear eliminator's var queue
    fn clear_var_queue(&mut self, vdb: &mut VarDB) {
        self.var_queue.clear(vdb);
    }
    /// return the length of eliminator's var queue.
    fn var_queue_len(&self) -> usize {
        self.var_queue.len()
    }
}

fn try_subsume(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    vdb: &mut VarDB,
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
            elim.remove_cid_occur(vdb, did, &mut cdb[did]);
            if !cdb[did].is(Flag::LEARNT) {
                cdb[cid].turn_off(Flag::LEARNT);
            }
        }
        Some(l) => {
            // println!("BackSubC subsumes {} from {} and {}", l.int(), cid.format(), did.format());
            strengthen_clause(cdb, elim, vdb, asgs, did, !l)?;
            elim.enqueue_var(vdb, l.vi(), true);
        }
        None => {}
    }
    Ok(())
}

/// returns a literal if these clauses can be merged by the literal.
fn subsume(cdb: &mut ClauseDB, cid: ClauseId, other: ClauseId) -> Option<Lit> {
    debug_assert!(!other.is_lifted_lit());
    if cid.is_lifted_lit() {
        let l = Lit::from(cid);
        let oh = &cdb[other];
        for lo in &oh.lits {
            if l == !*lo {
                return Some(l);
            }
        }
        return None;
    }
    let mut ret: Lit = NULL_LIT;
    let ch = &cdb[cid];
    let ob = &cdb[other];
    debug_assert!(ob.lits.contains(&ob[0]));
    debug_assert!(ob.lits.contains(&ob[1]));
    'next: for l in &ch.lits {
        for lo in &ob.lits {
            if *l == *lo {
                continue 'next;
            } else if ret == NULL_LIT && *l == !*lo {
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
/// - `(true, n)` if they are mergeable to a n-literal clause.
fn check_to_merge(
    cdb: &ClauseDB,
    vdb: &VarDB,
    cp: ClauseId,
    cq: ClauseId,
    v: VarId,
) -> (bool, usize) {
    let pqb = &cdb[cp];
    let qpb = &cdb[cq];
    let ps_smallest = pqb.len() < qpb.len();
    let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
    let mut size = pb.lits.len() + 1;
    'next_literal: for l in &qb.lits {
        if vdb[l.vi()].is(Flag::ELIMINATED) {
            continue;
        }
        if l.vi() != v {
            for j in &pb.lits {
                if vdb[j.vi()].is(Flag::ELIMINATED) {
                    continue;
                }
                if j.vi() == l.vi() {
                    if !*j == *l {
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
fn check_eliminator(cdb: &ClauseDB, vdb: &[Var]) -> bool {
    // clause_queue should be clear.
    // all elements in occur_lists exist.
    // for v in vdb {
    //     for ci in &v.pos_occurs {
    //         let c = clause!(cp, ci);
    //         if c[0] < 2 || c[1] < 2 {
    //             panic!("panic {:#}", c);
    //         }
    //     }
    //     for ci in &v.neg_occurs {
    //         let c = clause!(cp, ci);
    //         if c[0] < 2 || c[1] < 2 {
    //             panic!("panic {:#}", c);
    //         }
    //     }
    // }
    // all clauses are registered in corresponding occur_lists
    for (cid, c) in cdb[0..].iter().enumerate().skip(1) {
        if c.is(Flag::DEAD) {
            continue;
        }
        for l in &c.lits {
            let v = l.vi();
            if bool::from(*l) {
                if !vdb[v].pos_occurs.contains(&(ClauseId::from(cid))) {
                    panic!("failed to check {} {:#}", (ClauseId::from(cid)).format(), c);
                }
            } else if !vdb[v].neg_occurs.contains(&(ClauseId::from(cid))) {
                panic!("failed to check {} {:#}", (ClauseId::from(cid)).format(), c);
            }
        }
    }
    true
}

/// Returns **false** if one of the clauses is always satisfied. (merge_vec should not be used.)
fn merge(cdb: &mut ClauseDB, cip: ClauseId, ciq: ClauseId, v: VarId, vec: &mut Vec<Lit>) -> usize {
    vec.clear();
    let pqb = &cdb[cip];
    let qpb = &cdb[ciq];
    let ps_smallest = pqb.len() < qpb.len();
    let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
    // println!(" -  {:?}{:?} & {:?}{:?}", vec2int(&ph.lit),vec2int(&pb.lits),vec2int(&qh.lit),vec2int(&qb.lits));
    'next_literal: for l in &qb.lits {
        if l.vi() != v {
            for j in &pb.lits {
                if j.vi() == l.vi() {
                    if !*j == *l {
                        return 0;
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
    vec.len()
}

/// removes `l` from clause `cid`
/// - calls `enqueue_clause`
/// - calls `enqueue_var`
fn strengthen_clause(
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    vdb: &mut VarDB,
    asgs: &mut AssignStack,
    cid: ClauseId,
    l: Lit,
) -> MaybeInconsistent {
    debug_assert!(!cdb[cid].is(Flag::DEAD));
    debug_assert!(1 < cdb[cid].len());
    cdb.touched[l] = true;
    cdb.touched[!l] = true;
    debug_assert_ne!(cid, ClauseId::default());
    if strengthen(cdb, cid, l) {
        // Vaporize the binary clause
        debug_assert!(2 == cdb[cid].len());
        let c0 = cdb[cid][0];
        debug_assert_ne!(c0, l);
        // println!("{} {:?} is removed and its first literal {} is enqueued.", cid.format(), vec2int(&cdb.clause[cid].lits), c0.int());
        cdb.detach(cid);
        elim.remove_cid_occur(vdb, cid, &mut cdb[cid]);
        asgs.assign_at_rootlevel(vdb, c0)
    } else {
        // println!("cid {} drops literal {}", cid.fmt(), l.int());
        debug_assert!(1 < cdb[cid].len());
        elim.enqueue_clause(cid, &mut cdb[cid]);
        elim.remove_lit_occur(vdb, l, cid);
        unsafe {
            let vec = &cdb[cid].lits[..] as *const [Lit];
            cdb.certificate_add(&*vec);
        }
        Ok(())
    }
}

/// removes Lit `p` from Clause *self*. This is an O(n) function!
/// returns true if the clause became a unit clause.
/// Called only from strengthen_clause
fn strengthen(cdb: &mut ClauseDB, cid: ClauseId, p: Lit) -> bool {
    debug_assert!(!cdb[cid].is(Flag::DEAD));
    debug_assert!(1 < cdb[cid].len());
    let c = &mut cdb[cid];
    // debug_assert!((*ch).lits.contains(&p));
    // debug_assert!(1 < (*ch).len());
    if (*c).is(Flag::DEAD) {
        return false;
    }
    debug_assert!(1 < usize::from(!p));
    let lits = &mut (*c).lits;
    debug_assert!(1 < lits.len());
    if lits.len() == 2 {
        if lits[0] == p {
            lits.swap(0, 1);
        }
        debug_assert!(1 < usize::from(!lits[0]));
        return true;
    }
    if lits[0] == p || lits[1] == p {
        let (q, r) = if lits[0] == p {
            lits.swap_remove(0);
            (lits[0], lits[1])
        } else {
            lits.swap_remove(1);
            (lits[1], lits[0])
        };
        debug_assert!(1 < usize::from(!p));
        let len = lits.len();
        cdb.watcher[!p].detach_with(cid);
        cdb.watcher[!q].register(r, cid);
        if len == 2 {
            // update another bocker
            cdb.watcher[!r].update_blocker(cid, q);
        }
    } else {
        lits.delete_unstable(|&x| x == p);
        if lits.len() == 2 {
            // update another bocker
            let q = lits[0];
            let r = lits[1];
            cdb.watcher[!q].update_blocker(cid, r);
            cdb.watcher[!r].update_blocker(cid, q);
        }
    }
    false
}

fn make_eliminating_unit_clause(vec: &mut Vec<Lit>, x: Lit) {
    vec.push(x);
    vec.push(Lit::from(1usize));
}

fn make_eliminated_clause(cdb: &mut ClauseDB, vec: &mut Vec<Lit>, vi: VarId, cid: ClauseId) {
    let first = vec.len();
    // Copy clause to the vector. Remember the position where the variable 'v' occurs:
    let c = &cdb[cid];
    debug_assert!(!c.is_empty());
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
    vec.push(Lit::from(c.len()));
    cdb.touched[Lit::from_assign(vi, true)] = true;
    cdb.touched[Lit::from_assign(vi, false)] = true;
    // println!("make_eliminated_clause: eliminate({}) clause {:?}", vi, vec2int(&ch.lits));
}

fn eliminate_var(
    asgs: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    state: &mut State,
    vdb: &mut VarDB,
    vi: VarId,
    timedout: &Arc<AtomicBool>,
) -> MaybeInconsistent {
    let v = &mut vdb[vi];
    if v.assign.is_some() {
        return Ok(());
    }
    debug_assert!(!v.is(Flag::ELIMINATED));
    // count only alive clauses
    v.pos_occurs.retain(|&c| !cdb[c].is(Flag::DEAD));
    v.neg_occurs.retain(|&c| !cdb[c].is(Flag::DEAD));
    let pos = &v.pos_occurs as *const Vec<ClauseId>;
    let neg = &v.neg_occurs as *const Vec<ClauseId>;
    unsafe {
        if skip_var_elimination(cdb, elim, vdb, &*pos, &*neg, vi) {
            return Ok(());
        }
        // OK, eliminate the literal and build constraints on it.
        state.num_eliminated_vars += 1;
        make_eliminated_clauses(cdb, elim, vi, &*pos, &*neg);
        let vec = &mut state.new_learnt as *mut Vec<Lit>;
        // Produce clauses in cross product:
        for p in &*pos {
            let rank_p = cdb[p].rank;
            for n in &*neg {
                // println!("eliminator replaces {} with a cross product {:?}", p.fmt(), vec2int(&vec));
                match merge(cdb, *p, *n, vi, &mut *vec) {
                    0 => (),
                    1 => {
                        // println!(
                        //     "eliminate_var: grounds {} from {}{:?} and {}{:?}",
                        //     vec[0].int(),
                        //     p.fmt(),
                        //     vec2int(&clause!(*cp, *p).lits),
                        //     n.fmt(),
                        //     vec2int(&clause!(*cp, *n).lits)
                        // );
                        let lit = (*vec)[0];
                        cdb.certificate_add(&*vec);
                        asgs.assign_at_rootlevel(vdb, lit)?;
                    }
                    _ => {
                        let rank = if cdb[p].is(Flag::LEARNT) && cdb[n].is(Flag::LEARNT) {
                            rank_p.min(cdb[n].rank)
                        } else {
                            0
                        };
                        let cid = cdb.attach(state, vdb, rank);
                        elim.add_cid_occur(vdb, cid, &mut cdb[cid], true);
                    }
                }
            }
        }
        for cid in &*pos {
            cdb.detach(*cid);
            elim.remove_cid_occur(vdb, *cid, &mut cdb[cid]);
        }
        for cid in &*neg {
            cdb.detach(*cid);
            elim.remove_cid_occur(vdb, *cid, &mut cdb[cid]);
        }
        vdb[vi].pos_occurs.clear();
        vdb[vi].neg_occurs.clear();
        vdb[vi].turn_on(Flag::ELIMINATED);
        elim.backward_subsumption_check(asgs, cdb, vdb, timedout)
    }
}

/// returns `true` if elimination is impossible.
fn skip_var_elimination(
    cdb: &ClauseDB,
    elim: &mut Eliminator,
    vdb: &VarDB,
    pos: &[ClauseId],
    neg: &[ClauseId],
    v: VarId,
) -> bool {
    // avoid thrashing
    if 0 < cdb.soft_limit && cdb.soft_limit < cdb.count(true) {
        return true;
    }
    let limit = if 0 < cdb.soft_limit && 3 * cdb.soft_limit < 4 * cdb.count(true) {
        elim.eliminate_grow_limit / 4
    } else {
        elim.eliminate_grow_limit
    };
    let clslen = pos.len() + neg.len();
    let mut cnt = 0;
    for c_pos in pos {
        for c_neg in neg {
            let (res, clause_size) = check_to_merge(cdb, vdb, *c_pos, *c_neg, v);
            if res {
                cnt += 1;
                if clslen + limit < cnt
                    || (elim.eliminate_combination_limit != 0
                        && elim.eliminate_combination_limit < clause_size)
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
            debug_assert!(!cdb[cid].is(Flag::DEAD));
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from_assign(v, true));
    } else {
        for cid in pos {
            debug_assert!(!cdb[cid].is(Flag::DEAD));
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from_assign(v, false));
    }
}

impl Var {
    fn occur_activity(&self) -> usize {
        self.pos_occurs.len().min(self.neg_occurs.len())
    }
}

/// Var heap structure based on the number of occurrences
// # Note
// - both fields has a fixed length. Don't use push and pop.
// - `idxs[0]` contains the number of alive elements
//   `indx` is positions. So the unused field 0 can hold the last position as a special case.
#[derive(Debug)]
pub struct VarOccHeap {
    heap: Vec<VarId>, // order : usize -> VarId
    idxs: Vec<usize>, // VarId : -> order : usize
}

trait VarOrderIF {
    fn new(n: usize, init: usize) -> VarOccHeap;
    fn insert(&mut self, vec: &VarDB, vi: VarId, upword: bool);
    fn clear(&mut self, vdb: &mut VarDB);
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn select_var(&mut self, vdb: &VarDB) -> Option<VarId>;
    fn rebuild(&mut self, vdb: &VarDB);
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
    fn insert(&mut self, vdb: &VarDB, vi: VarId, upward: bool) {
        debug_assert!(vi < self.heap.len());
        if self.contains(vi) {
            let i = self.idxs[vi];
            if upward {
                self.percolate_up(vdb, i);
            } else {
                self.percolate_down(vdb, i);
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
        self.percolate_up(vdb, n);
    }
    fn clear(&mut self, vdb: &mut VarDB) {
        for v in &mut self.heap[0..self.idxs[0]] {
            vdb[*v].turn_off(Flag::ENQUEUED);
        }
        self.reset()
    }
    fn len(&self) -> usize {
        self.idxs[0]
    }
    fn is_empty(&self) -> bool {
        self.idxs[0] == 0
    }
    fn select_var(&mut self, vdb: &VarDB) -> Option<VarId> {
        loop {
            let vi = self.get_root(vdb);
            if vi == 0 {
                return None;
            }
            if !vdb[vi].is(Flag::ELIMINATED) {
                return Some(vi);
            }
        }
    }
    fn rebuild(&mut self, vdb: &VarDB) {
        self.reset();
        for v in &vdb[1..] {
            if v.assign.is_none() && !v.is(Flag::ELIMINATED) {
                self.insert(vdb, v.index, true);
            }
        }
    }
}

impl VarOccHeap {
    fn contains(&self, v: VarId) -> bool {
        self.idxs[v] <= self.idxs[0]
    }
    fn reset(&mut self) {
        for i in 0..self.idxs.len() {
            self.idxs[i] = i;
            self.heap[i] = i;
        }
    }
    fn get_root(&mut self, vdb: &VarDB) -> VarId {
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
            self.percolate_down(&vdb, 1);
        }
        vs
    }
    fn percolate_up(&mut self, vdb: &VarDB, start: usize) {
        let mut q = start;
        let vq = self.heap[q];
        debug_assert!(0 < vq, "size of heap is too small");
        let aq = vdb[vq].occur_activity();
        loop {
            let p = q / 2;
            if p == 0 {
                self.heap[q] = vq;
                debug_assert!(vq != 0, "Invalid index in percolate_up");
                self.idxs[vq] = q;
                return;
            } else {
                let vp = self.heap[p];
                let ap = vdb[vp].occur_activity();
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
    fn percolate_down(&mut self, vdb: &VarDB, start: usize) {
        let n = self.len();
        let mut i = start;
        let vi = self.heap[i];
        let ai = vdb[vi].occur_activity();
        loop {
            let l = 2 * i; // left
            if l < n {
                let vl = self.heap[l];
                let al = vdb[vl].occur_activity();
                let r = l + 1; // right
                let (target, vc, ac) = if r < n && al > vdb[self.heap[r]].occur_activity() {
                    let vr = self.heap[r];
                    (r, vr, vdb[vr].occur_activity())
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
    fn remove(&mut self, vec: &VarDB, vs: VarId) {
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

#[cfg(test)]
mod tests {
    #![allow(unused_imports)]
    #![allow(unused_variables)]
    #![allow(dead_code)]
    use {super::*, crate::solver::Solver};

    macro_rules! mkv {
        ($($x:expr),*) => {
            match &[$($x),*] {
                v => v.iter().map(|x| Lit::from(*x as i32)).collect::<Vec<Lit>>(),
            }
        };
    }

    #[test]
    fn check_occurs() {
        let cfg: Config = Default::default();
        let cnf: CNFDescription = CNFDescription {
            num_of_variables: 10,
            num_of_clauses: 10,
            pathname: "".to_string(),
        };
        let mut s = Solver::instantiate(&cfg, &cnf);

        let c1 = s.cdb.new_clause(&mkv![1, 2, 3], 3, true);
        let c2 = s.cdb.new_clause(&mkv![-2, 3, 4], 3, true);
        let c3 = s.cdb.new_clause(&mkv![-2, -3], 2, true);
        let c4 = s.cdb.new_clause(&mkv![1, 2, -3, 9], 4, true);
        //    {
        //        let vec = [&c2, &c3]; // [&c1, &c2, &c3, &c4];
        //        for x in &vec {
        //            for y in &vec {
        //                println!(
        //                    "{}\tsubsumes\t{}\t=>\t{:?}",
        //                    x,
        //                    y,
        //                    x.subsumes(&y).map(|l| l.int())
        //                );
        //            }
        //        }
        //    }
        //    // s.attach_clause(c1);
        //    s.attach_clause(c2);
        //    s.attach_clause(c3);
        //    // s.attach_clause(c4);
        //    // s.vars.dump("##added");
        //    println!("{:?}", s.eliminator);
        //    s.eliminate();
        //    // s.vars.dump("##eliminated");
        //    println!("{:?}", s.eliminator);
        //    println!("::done");
    }

    fn mk_c(s: &mut Solver, i: usize, v: Vec<i32>) -> ClauseId {
        let vec = v.iter().map(|i| Lit::from(*i)).collect::<Vec<Lit>>();
        let cid = s.cdb.new_clause(&vec, vec.len(), true);
        cid
    }
}

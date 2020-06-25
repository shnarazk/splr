//! Vivification
#![allow(dead_code)]
use {
    super::{conflict::conflict_analyze, SolverEvent, State},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        state::StateIF,
        types::*,
    },
    std::collections::{HashMap, HashSet},
};

/// map a Lit to a pair of dirty bit and depending clauses.
type ConflictDepEntry = (bool, HashSet<ClauseId>, Vec<Lit>);

struct ConflictDep {
    body: HashMap<Lit, ConflictDepEntry>,
}

impl ConflictDep {
    fn new() -> Self {
        ConflictDep {
            body: HashMap::new(),
        }
    }
    fn get(&self, l: Lit) -> Option<&ConflictDepEntry> {
        self.body.get(&l)
    }
    fn put(&mut self, l: Lit, cid: ClauseId, c: &Clause) {
        if let Some(e) = &mut self.body.get_mut(&l) {
            e.0 = true;
            e.1.insert(cid);
            e.2 = c.lits.clone();
        } else {
            let mut h = HashSet::new();
            h.insert(cid);
            self.body.insert(l, (true, h, c.lits.clone()));
        }
    }
    fn purge(&mut self, l: Lit) {
        if let Some(e) = &mut self.body.get_mut(&l) {
            e.0 = false;
            e.1.clear();
            e.2.clear();
        }
    }
}

pub fn vivify(asg: &mut AssignStack, cdb: &mut ClauseDB, state: &mut State, nseek_max: usize) {
    state.flush("vivifying...");
    asg.handle(SolverEvent::Vivify(true));
    let mut cache: HashSet<Lit> = HashSet::new();
    const NSHRINK: usize = 4_000;
    let mut nseek: usize = 0;
    let mut nshrink = 0;
    let mut nassign = 0;
    let mut change: bool = true;
    assert_eq!(asg.decision_level(), asg.root_level);
    while change {
        change = false;
        let mut clauses: Vec<ClauseId> = Vec::new();
        for (i, c) in cdb.iter_mut().enumerate().skip(1) {
            if !c.is(Flag::DEAD) && 2 < c.len() {
                clauses.push(ClauseId::from(i));
            }
        }
        // clauses.sort_by_cached_key(|c| 1 - cdb[c].len() as i32);
        clauses.sort_by_cached_key(|c| cdb.activity(*c) as isize);

        for ci in clauses.iter().rev() {
            let c: &Clause = &cdb[ci];
            if c.is(Flag::DEAD) {
                continue;
            }
            let is_learnt = c.is(Flag::LEARNT);
            let clits = c.lits.clone();
            let c_len = clits.len();
            cdb.detach(*ci);
            cdb.garbage_collect();
            let mut shortened = false;
            let mut i = 0;
            let mut new_clauses: Vec<Vec<Lit>> = Vec::new();
            while !shortened && i < c_len {
                let l = &clits[i]; // select_a_literal(cx);
                i += 1;
                if i % 20 == 0 {
                    state.flush("");
                    state.flush(format!("vivifying({}, {}, {})...", nassign, nshrink, nseek));
                }
                if asg.assigned(*l).is_some() {
                    continue;
                }
                asg.assign_by_decision(!*l); // Σb ← (Σb ∪ {¬l})
                let nassign_before_propagation = asg.stack_len();
                let confl = if cache.contains(&!*l) {
                    ClauseId::default()
                } else {
                    asg.propagate(cdb)
                };
                nseek += 1;
                if confl != ClauseId::default() {
                    // ⊥ ∈ UP(Σb)
                    conflict_analyze(asg, cdb, state, confl); // returns a learnt clause
                    let learnt = &state.new_learnt;
                    if learnt.iter().all(|l| clits.contains(l)) {
                        // cl ⊂ c
                        new_clauses.push(learnt.clone()); // MODIFIED: Σ ← Σ ∪ {cl}
                        shortened = true;
                        nshrink += 1;
                    } else {
                        if learnt.len() < c_len {
                            new_clauses.push(learnt.clone()); // MODIFIED: Σ ← Σ ∪ {cl}
                            i = c_len; // a trick to exit the loop
                        }
                        // assert_eq!(i, cb.len());
                        if c_len != i {
                            let temp = clits[..i].to_vec();
                            assert!(1 < temp.len());
                            new_clauses.push(temp); // MODIFIED: Σ ← Σ ∪ {cb}
                            shortened = true;
                            nshrink += 1;
                        }
                    }
                } else if asg.stack_len() == nassign_before_propagation {
                    cache.insert(!*l);
                } else {
                    // `i` was incremented.
                    if let Some(ls) = clits[i..].iter().find(|l| asg.assigned(**l) == Some(true)) {
                        // ∃(ls ∈ (c\cb))
                        if 1 < c_len - i {
                            // (c\cb) /= {ls}
                            let mut temp = clits[..i].to_vec();
                            temp.push(*ls);
                            assert!(1 < temp.len());
                            new_clauses.push(temp); // MODIFIED: Σ ← Σ ∪ {cb ∪ {ls}} ;
                            shortened = true;
                            nshrink += 1;
                        }
                    }
                    if let Some(ls) = clits[i..].iter().find(|l| asg.assigned(!**l) == Some(true)) {
                        // ∃(¬Ls ∈ (c\cb))
                        let temp: Vec<Lit> = clits
                            .iter()
                            .map(|l| *l)
                            .filter(|l| l != ls)
                            .collect::<Vec<_>>();
                        assert!(1 < temp.len());
                        new_clauses.push(temp); // MODIFIED: Σ ← Σ ∪ {c\{ls}}
                        shortened = true;
                        nshrink += 1;
                    }
                }
                if !shortened {
                    let mut cls = clits.clone();
                    cdb.new_clause(asg, &mut cls, false, false);
                } else {
                    change = true;
                }
                asg.cancel_until(asg.root_level);
                debug_assert!(asg.assigned(*l).is_none());
                // cdb.eliminate_satisfied_clauses(asg, elim, false);
            }
            for c in &mut new_clauses {
                if c.len() == 1 {
                    nassign += 1;
                    asg.assign_at_rootlevel(c[0]).expect("impossible");
                    asg.handle(SolverEvent::Fixed);
                } else {
                    cdb.new_clause(asg, c, is_learnt, false);
                }
            }
            if !new_clauses.is_empty() {
                cache.clear();
            }
            if NSHRINK < nshrink || nseek_max < nseek {
                break;
            }
        }
        if NSHRINK < nshrink || nseek_max < nseek {
            change = false;
        }
    }
    asg.handle(SolverEvent::Vivify(false));
    state.flush("");
    state.flush(format!("vivified({}, {})", nassign, nshrink));
}

fn conflict_analyze_2(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    conflicting_clause: ClauseId,
) -> HashSet<ClauseId> {
    let mut seen: HashSet<VarId> = HashSet::new();
    let mut set: HashSet<ClauseId> = HashSet::new();
    let dl = asg.decision_level();
    let mut p = cdb[conflicting_clause].lits[0];
    let vi = p.vi();
    if !seen.contains(&vi) && 0 < asg.level(vi) {
        seen.insert(vi);
    }
    let mut reason = AssignReason::Implication(conflicting_clause, NULL_LIT);
    let mut ti = asg.stack_len() - 1; // trail index
    loop {
        match reason {
            AssignReason::Implication(_, l) if l != NULL_LIT => {
                let vi = l.vi();
                if !seen.contains(&vi) {
                    let lvl = asg.level(vi);
                    if 0 == lvl {
                        continue;
                    }
                    seen.insert(vi);
                }
            }
            AssignReason::Implication(cid, _) => {
                set.insert(cid);
                let c = &cdb[cid];
                for q in &c[1..] {
                    let vi = q.vi();
                    if !seen.contains(&vi) {
                        let lvl = asg.level(vi);
                        if 0 == lvl {
                            continue;
                        }
                        seen.insert(vi);
                    }
                }
            }
            _ => (),
        }
        if ti == 0 {
            break;
        }
        while {
            let vi = asg.stack(ti).vi();
            let lvl = asg.level(vi);
            !seen.contains(&vi) || lvl != dl
        } {
            ti -= 1;
            if ti == 0 {
                break;
            }
        }
        p = asg.stack(ti);
        seen.remove(&p.vi());
        if ti == 0 {
            break;
        }
        ti -= 1;
        reason = asg.reason(p.vi());
    }
    set
}

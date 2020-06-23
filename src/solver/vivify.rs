//! Vivification
use {
    super::{conflict::conflict_analyze, State},
    crate::{
        assign::{AssignIF, AssignStack, PropagateIF, VarManipulateIF},
        cdb::{ClauseDB, ClauseDBIF},
        processor::Eliminator,
        state::StateIF,
        types::*,
    },
};

pub fn vivify(asg: &mut AssignStack, cdb: &mut ClauseDB, elim: &mut Eliminator, state: &mut State) {
    state.flush("vivifying...");
    let mut change: bool = true;
    assert_eq!(asg.decision_level(), asg.root_level);
    while change {
        // assert!(asg.propagate(cdb) == ClauseId::default());
        // cdb.garbage_collect();
        change = false;
        let mut i: usize = 1; // skip NULL_CLAUSE
        let num_c = cdb.len();
        // println!("loop start:: num_c: {}, asg: {}", num_c, asg);
        while i < num_c {
            let ci = ClauseId::from(i);
            i += 1;
            if i % 10 == 0 {
                state.flush("");
                state.flush(format!("vivifying: {}...", i));
            }
            let c: &Clause = &cdb[ci];
            let c_len = c.lits.len();
            if c.is(Flag::DEAD) || c_len < 4 || c.is(Flag::LEARNT) {
                continue;
            }
            // println!("{}:{}", ci, c);
            let c_lits = c.lits.clone();
            assert!(!cdb[ci].is(Flag::DEAD));
            cdb.detach(ci);
            cdb.eliminate_satisfied_clauses(asg, elim, false);
            cdb.garbage_collect();
            // let mut cb: Vec<Lit> = Vec::new();
            let mut shortened = false;
            let mut i = 0;
            let mut clauses: Vec<Vec<Lit>> = Vec::new();
            assert!(1 < c_len && 1 < c_lits.len() && c_len == c_lits.len());
            while !shortened && i < c_len
            /* c != cb */
            {
                // let cx = c_lits.remove_items(cb);
                // let l: Lit = select_a_literal(cx);
                let l = &c_lits[i];
                i += 1;
                // cb.push(*l); // cb = cb ∪ {l};
                if asg.assigned(*l).is_some() {
                    continue;
                }
                asg.assign_by_decision(!*l); // Σb ← (Σb ∪ {¬l})
                                             // asg.assign_by_implication(!*l, AssignReason::Implication(ci, !*l), asg.root_level);
                                             // println!("assign {} on {}", !*l, asg);
                let confl = asg.propagate(cdb);
                if confl != ClauseId::default() {
                    // ⊥ ∈ UP(Σb)
                    conflict_analyze(asg, cdb, state, confl); // returns a learnt clause
                    let learnt = &state.new_learnt;
                    if learnt.iter().all(|l| c_lits.contains(l)) {
                        // cl ⊂ c
                        assert!(0 < learnt.clone().len());
                        clauses.push(learnt.clone()); // MODIFIED: Σ ← Σ ∪ {cl}
                        shortened = true;
                    } else {
                        if learnt.len() == c_len {
                            assert!(1 < learnt.clone().len());
                            clauses.push(learnt.clone()); // MODIFIED: Σ ← Σ ∪ {cl}
                            i = c_len; // a trick to exit the loop
                                       // cb.clear();
                                       // for l in &c_lits {
                                       //     cb.push(*l);
                                       // }
                        }
                        // assert_eq!(i, cb.len());
                        if c_len != i {
                            let temp = c_lits[..i].to_vec();
                            //std::mem::swap(&mut temp, &mut cb);
                            assert!(1 < temp.len());
                            clauses.push(temp); // MODIFIED: Σ ← Σ ∪ {cb}
                            shortened = true;
                        }
                    }
                } else {
                    // `i` was incremented.
                    if let Some(ls) = /* cx */
                        c_lits[i..].iter().find(|l| asg.assigned(**l) == Some(true))
                    {
                        // ∃(ls ∈ (c\cb))
                        if 1 < c_len - i
                        /* cx.len() */
                        {
                            // (c\cb) /= {ls}
                            // assert!(1 <= cb.len());
                            // cb.push(*ls);
                            let mut temp = c_lits[..i].to_vec();
                            temp.push(*ls);
                            // std::mem::swap(&mut temp, &mut cb);
                            assert!(1 < temp.len());
                            clauses.push(temp); // MODIFIED: Σ ← Σ ∪ {cb ∪ {ls}} ;
                            shortened = true;
                        }
                    }
                    if let Some(ls) = /* cx */ c_lits[i..]
                        .iter()
                        .find(|l| asg.assigned(!**l) == Some(true))
                    {
                        // ∃(¬Ls ∈ (c\cb))
                        let temp: Vec<Lit> = c_lits
                            .iter()
                            .map(|l| *l)
                            .filter(|l| l != ls)
                            .collect::<Vec<_>>();
                        assert!(1 < temp.len());
                        clauses.push(temp); // MODIFIED: Σ ← Σ ∪ {c\{ls}}
                        shortened = true;
                    }
                }
                // println!("loop end:: i: {}, c_len: {}, lits: {:?}", i, c_len, c_lits);
                if !shortened {
                    assert!(1 < c_lits.len());
                    cdb.new_clause(asg, &mut c_lits.clone(), false, false);
                // println!("push back");
                } else {
                    change = true;
                }
                asg.cancel_until(asg.root_level);
                assert!(asg.assigned(*l).is_none());
                cdb.eliminate_satisfied_clauses(asg, elim, false);
            }
            for c in &mut clauses {
                if c.len() == 1 {
                    asg.assign_at_rootlevel(c[0]).expect("impossible");
                } else {
                    assert!(1 < c.len(), format!("c's length is {}", c.len()));
                    cdb.new_clause(asg, c, false, false);
                }
            }
        }
        // println!("loop end:: ci: {}, cdb: {}, changed: {}", ci, num_c, change);
        change = false;
    }
}

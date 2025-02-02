/// Module `eliminator` implements clause subsumption and var elimination.
use {
    super::Eliminator,
    crate::{assign::AssignIF, cdb::ClauseDBIF, solver::SolverEvent, state::State, types::*},
};

// Stop elimination if a generated resolvent is larger than this
const COMBINATION_LIMIT: f64 = 32.0;

pub fn eliminate_var<'a>(
    asg: &mut AssignStack<'a>,
    vars: &mut [Var<'a>],
    cdb: &mut ClauseDB<'a>,
    elim: &mut Eliminator<'a>,
    state: &mut State,
    vi: VarId,
    timedout: &mut usize,
) -> MaybeInconsistent {
    let v = &mut vars[vi];
    let w = &mut elim.var[vi];
    if v.assign.is_some() || w.aborted {
        return Ok(());
    }
    debug_assert!(!v.is(FlagVar::ELIMINATED));
    // count only alive clauses
    // Note: it may contain the target literal somehow. So the following may be failed.
    // debug_assert!(w.pos_occurs.iter().all(|c| cdb[*c].is_dead() || cdb[*c].contains(Lit::from((vi, true)))));
    w.pos_occurs
        .retain(|&c| cdb[c].contains(Lit::from((&*v, false))));
    // debug_assert!(w.pos_occurs.iter().all(|c| cdb[*c].is_dead() || cdb[*c].contains(Lit::from((vi, false)))));
    w.neg_occurs
        .retain(|&c| cdb[c].contains(Lit::from((&*v, true))));

    let num_combination = w.pos_occurs.len() * w.neg_occurs.len();

    if *timedout < num_combination
        || skip_var_elimination(
            asg,
            cdb,
            &w.pos_occurs,
            &w.neg_occurs,
            vi,
            elim.eliminate_grow_limit,
        )
    {
        return Ok(());
    } else {
        *timedout -= num_combination;
    }
    let pos = w.pos_occurs.clone();
    let neg = w.neg_occurs.clone();
    #[cfg(feature = "trace_elimination")]
    println!("# eliminate_var {}", vi);
    // OK, eliminate the literal and build constraints on it.
    make_eliminated_clauses(cdb, &mut elim.elim_lits, vi, &pos, &neg);
    let vec = &mut state.new_learnt;
    // println!("eliminate_var {}: |p|: {} and |n|: {}", vi, (*pos).len(), (*neg).len());
    // Produce clauses in cross product:
    for p in pos.iter() {
        let learnt_p = cdb[*p].is(FlagClause::LEARNT);
        for n in neg.iter() {
            match merge(asg, cdb, *p, *n, vi, vec) {
                0 => {
                    #[cfg(feature = "trace_elimination")]
                    println!(
                        " - eliminate_var {}: fusion {}{} and {}{}",
                        vi, p, cdb[*p], n, cdb[*n],
                    );
                }
                1 => {
                    let lit = vec[0];
                    #[cfg(feature = "trace_elimination")]
                    println!(
                        " - eliminate_var {}: found assign {} from {}{} and {}{}",
                        vi, lit, p, cdb[*p], n, cdb[*n],
                    );
                    match lit.assigned() {
                        Some(true) => (),
                        Some(false) => {
                            return Err(SolverError::RootLevelConflict);
                        }
                        None => {
                            debug_assert!(lit.assigned().is_none());
                            cdb.certificate_add_assertion(lit);
                            asg.assign_at_root_level(lit)?;
                        }
                    }
                }
                _ => {
                    debug_assert!(vec.iter().all(|l| !vec.contains(&!*l)));
                    match cdb.new_clause(asg, vec, learnt_p && cdb[*n].is(FlagClause::LEARNT)) {
                        RefClause::Clause(ci) => {
                            // the merged clause might be a duplicated clause.
                            elim.add_cid_occur(vars, asg, ci, &mut cdb[ci], true);

                            #[cfg(feature = "trace_elimination")]
                            println!(
                                " - eliminate_var {}: X {} from {} and {}",
                                vi, cdb[ci], cdb[*p], cdb[*n],
                            );
                        }
                        RefClause::Dead => (),
                        RefClause::EmptyClause => (),
                        RefClause::RegisteredClause(_) => (),
                        RefClause::UnitClause(_) => (),
                    }
                }
            }
        }
    }
    //
    //## VAR ELIMINATION
    //
    debug_assert!(pos.iter().all(|cid| !cdb[*cid].is_dead()));
    debug_assert!(neg.iter().all(|cid| !cdb[*cid].is_dead()));
    for cid in pos.iter() {
        if cdb[*cid].is_dead() {
            continue;
        }
        elim.remove_cid_occur(asg, *cid, &mut cdb[*cid]);
        cdb.remove_clause(*cid);
    }
    for cid in neg.iter() {
        if cdb[*cid].is_dead() {
            continue;
        }
        elim.remove_cid_occur(asg, *cid, &mut cdb[*cid]);
        cdb.remove_clause(*cid);
    }
    elim[vi].clear();
    make_var_eliminated(asg, vam, state.restart, vi);
    elim.backward_subsumption_check(asg, cdb, timedout)
}

/// returns `true` if elimination is impossible.
fn skip_var_elimination(
    asg: &impl AssignIF,
    cdb: &impl ClauseDBIF,
    pos: &[ClauseId],
    neg: &[ClauseId],
    v: VarId,
    grow_limit: usize,
) -> bool {
    // avoid thrashing
    let limit = match cdb.check_size() {
        Ok(true) => grow_limit,
        Ok(false) => grow_limit / 4,
        Err(_) => return true,
    };
    let clslen = pos.len() + neg.len();
    let mut cnt = 0;
    let scale: f64 = 0.5;
    let mut average_len: f64 = 0.0;
    for c_pos in pos {
        for c_neg in neg {
            if let Some(clause_size) = merge_cost(asg, cdb, *c_pos, *c_neg, v) {
                if clause_size == 0 {
                    continue;
                }
                cnt += 1;
                average_len *= 1.0 - scale;
                average_len += scale * clause_size as f64;
                if clslen + limit < cnt || COMBINATION_LIMIT < average_len {
                    return true;
                }
            } else {
                debug_assert!(false, "impossible");
            }
        }
    }
    false
}

/// Returns the the-size-of-clause-being-generated.
/// - `(false, -)` if one of the clauses is always satisfied.
/// - `(true, n)` if they are merge-able to a n-literal clause.
fn merge_cost(
    asg: &impl AssignIF,
    cdb: &impl ClauseDBIF,
    cp: ClauseId,
    cq: ClauseId,
    vi: VarId,
) -> Option<usize> {
    let c_p = &cdb[cp];
    let c_q = &cdb[cq];
    let mut cond: Option<Lit> = None;
    let mut cond2: Option<Lit> = None;
    let mut count = 0;

    'next_lit: for lit in c_p.iter() {
        if lit.var.id == vi {
            cond = Some(*lit);
            continue;
        }
        debug_assert!(!lit.var.is(FlagVar::ELIMINATED));
        // if this is the last occurrence of this literal, count it.
        for l in c_q.iter() {
            if !*lit == *l {
                return Some(0);
            } else if *lit == *l || l.var.is(FlagVar::ELIMINATED) {
                continue 'next_lit;
            }
        }
        count += 1;
    }
    cond?;
    for lit in c_q.iter() {
        if lit.var.id == vi {
            if cond == Some(!*lit) {
                cond2 = Some(*lit);
                continue;
            } else {
                return None;
            }
        }
        debug_assert!(!lit.var.is(FlagVar::ELIMINATED));
        count += 1;
    }
    cond2.map(|_| count)
}

/// Return the real length of the generated clause by merging two clauses.
/// Return **zero** if one of the clauses is always satisfied. (merge_vec should not be used.)
fn merge(
    asg: &mut impl AssignIF<'a>,
    cdb: &mut impl ClauseDBIF<'a>,
    cip: ClauseId,
    ciq: ClauseId,
    vi: VarId,
    vec: &mut Vec<Lit>,
) -> usize {
    vec.clear();
    let pqb = &cdb[cip];
    let qpb = &cdb[ciq];
    let ps_smallest = pqb.len() < qpb.len();
    let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
    #[cfg(feature = "trace_elimination")]
    println!("# merge {} & {}", pb, qb);
    if pb
        .iter()
        .filter(|l| l.var.id != vi)
        .any(|l| qb.contains(!*l))
    {
        return 0;
    }

    let mut lits = pb
        .iter()
        .filter(|l| l.var.id != vi && !qb.contains(**l))
        .copied()
        .collect::<Vec<_>>();
    lits.append(
        &mut qb
            .iter()
            .filter(|l| l.var.id != vi)
            .copied()
            .collect::<Vec<_>>(),
    );
    std::mem::swap(&mut lits, vec);
    debug_assert!(vec.iter().all(|l| !l.var.is(FlagVar::ELIMINATED)));
    debug_assert!(vec.iter().all(|l| l.var.id != vi));
    vec.len()
}

fn make_eliminated_clauses(
    cdb: &mut impl ClauseDBIF<'a>,
    store: &mut Vec<Lit<'a>>,
    v: VarId,
    pos: &[ClauseId],
    neg: &[ClauseId],
) {
    if neg.len() < pos.len() {
        for cid in neg {
            debug_assert!(!cdb[*cid].is_dead());
            make_eliminated_clause(cdb, store, v, *cid);
        }
        make_eliminating_unit_clause(store, Lit::from((v, true)));
    } else {
        for cid in pos {
            debug_assert!(!cdb[*cid].is_dead());
            make_eliminated_clause(cdb, store, v, *cid);
        }
        make_eliminating_unit_clause(store, Lit::from((v, false)));
    }
}

fn make_eliminating_unit_clause(store: &mut Vec<Lit>, x: Lit) {
    #[cfg(feature = "trace_elimination")]
    println!(" - eliminator save {}", x);
    store.push(x);
    store.push(Lit::from(1usize));
}

fn make_eliminated_clause(
    cdb: &mut impl ClauseDBIF,
    store: &mut Vec<Lit>,
    vi: VarId,
    cid: ClauseId,
) {
    let first = store.len();
    // Copy clause to the vector. Remember the position where the variable 'v' occurs:
    let c = &cdb[cid];
    debug_assert!(!c.is_empty());
    for l in c.iter() {
        store.push(*l);
        if l.var.id == vi {
            let index = store.len() - 1;
            debug_assert_eq!(store[index], *l);
            debug_assert_eq!(store[index].var.id, vi);
            // swap the first literal with the 'v'. So that the literal containing 'v' will occur first in the clause.
            store.swap(index, first);
        }
    }
    // Store the length of the clause last:
    debug_assert_eq!(store[first].var.id, vi);
    store.push(Lit::from(c.len()));
    #[cfg(feature = "trace_elimination")]
    println!("# make_eliminated_clause: eliminate({}) clause {}", vi, c);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{cdb::ClauseDB, processor::EliminateIF, solver::Solver};
    use ::std::path::Path;

    impl Clause<'_> {
        #[allow(dead_code)]
        fn as_vec(&self) -> Vec<i32> {
            self.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
        }
    }
    impl ClauseDB<'_> {
        #[allow(dead_code)]
        fn as_vec(&self) -> Vec<Vec<i32>> {
            self.iter()
                .skip(1)
                .filter(|c| !c.is_dead())
                .map(|c| c.as_vec())
                .collect::<Vec<_>>()
        }
    }
    #[cfg(not(feature = "no_IO"))]
    #[test]
    fn test_eliminate_var() {
        let Solver {
            ref mut asg,
            ref mut cdb,
            ref mut state,
            ..
        } = Solver::try_from(Path::new("cnfs/uf8.cnf")).expect("failed to load");
        if !state.config.enable_eliminator {
            return;
        }
        let mut timedout = 10_000;
        let vi = 4;

        let mut elim = Eliminator::instantiate(&state.config, &state.cnf);
        elim.prepare(asg, cdb, true);
        eliminate_var(asg, cdb, &mut elim, state, vi, &mut timedout).expect("panic");
        assert!(asg.var(vi).is(FlagVar::ELIMINATED));
        assert!(cdb
            .iter()
            .skip(1)
            .filter(|c| c.is_dead())
            .all(|c| c.is_empty()));
        assert!(cdb
            .iter()
            .skip(1)
            .all(|c| c.iter().all(|l| *l != Lit::from((vi, false)))
                && c.iter().all(|l| *l != Lit::from((vi, false)))));
    }
}

/// Crate `eliminator` implements clause subsumption and var elimination.
use {
    super::{Eliminator, LitOccurs},
    crate::{
        assign::AssignIF,
        cdb::ClauseDBIF,
        solver::{restart::RestartIF, SolverEvent},
        state::State,
        types::*,
    },
};

pub fn eliminate_var<A, C, R>(
    asg: &mut A,
    cdb: &mut C,
    elim: &mut Eliminator,
    rst: &mut R,
    state: &mut State,
    vi: VarId,
    timedout: &mut usize,
) -> MaybeInconsistent
where
    A: AssignIF,
    C: ClauseDBIF,
    R: RestartIF,
{
    let v = &mut asg.var(vi);
    let w = &mut elim.var[vi];
    if asg.assign(vi).is_some() || w.aborted {
        return Ok(());
    }
    debug_assert!(!v.is(Flag::ELIMINATED));
    // count only alive clauses
    w.pos_occurs.retain(|&c| !cdb[c].is_dead());
    w.neg_occurs.retain(|&c| !cdb[c].is_dead());
    let LitOccurs {
        pos_occurs,
        neg_occurs,
        ..
    } = w;
    let pos = pos_occurs.clone();
    let neg = neg_occurs.clone();
    {
        if *timedout < pos.len() * neg.len()
            || skip_var_elimination(
                asg,
                cdb,
                &(*pos),
                &&(*neg),
                vi,
                elim.eliminate_grow_limit,
                elim.eliminate_combination_limit,
            )
        {
            return Ok(());
        } else {
            *timedout -= (*pos).len() * (*neg).len();
        }
        #[cfg(feature = "trace_elimination")]
        println!("# eliminate_var {}", vi);
        // OK, eliminate the literal and build constraints on it.
        make_eliminated_clauses(cdb, &mut elim.elim_lits, vi, &&(*pos), &&(*neg));
        let vec = &mut state.new_learnt;
        // println!("eliminate_var {}: |p|: {} and |n|: {}", vi, (*pos).len(), (*neg).len());
        // Produce clauses in cross product:
        for p in pos.iter() {
            let learnt_p = cdb[*p].is(Flag::LEARNT);
            for n in neg.iter() {
                match merge(cdb, *p, *n, vi, vec) {
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
                        match asg.assigned(lit) {
                            Some(true) => (),
                            Some(false) => {
                                return Err(SolverError::RootLevelConflict(ClauseId::from(lit)))
                            }
                            None => {
                                if asg.assign_at_root_level(lit).is_err() {
                                    return Err(SolverError::RootLevelConflict(ClauseId::from(
                                        lit,
                                    )));
                                }
                                cdb.certificate_add_assertion(lit);
                            }
                        }
                    }
                    _ => {
                        debug_assert!(vec.iter().all(|l| !vec.contains(&!*l)));
                        if let Some(cid) = cdb
                            .new_clause(asg, vec, learnt_p && cdb[*n].is(Flag::LEARNT))
                            .is_new()
                        {
                            elim.add_cid_occur(asg, cid, &mut cdb[cid], true);
                            #[cfg(feature = "trace_elimination")]
                            println!(
                                " - eliminate_var {}: X {} from {} and {}",
                                vi, cdb[cid], cdb[*p], cdb[*n],
                            );
                        }
                    }
                }
            }
        }
        //
        //## VAR ELIMINATION
        //
        assert!(pos.iter().all(|cid| !cdb[*cid].is_dead()));
        assert!(neg.iter().all(|cid| !cdb[*cid].is_dead()));
        for cid in pos.iter() {
            let a = *cid;
            debug_assert!(!asg.locked(&cdb[*cid], *cid));
            #[cfg(feature = "incremental_solver")]
            {
                if !cdb[*cid].is(Flag::LEARNT) {
                    cdb.make_permanent_immortal(*cid);
                }
            }
            assert!(!cdb[a].is_dead(), "eaeaeaebr!!!!{}{:?}", cid, cdb[a]);
            elim.remove_cid_occur(asg, a, &mut cdb[a]);
            // cdb.watches(a, "elminate::eliminate_var::129");
            cdb.remove_clause(a);
        }
        for cid in neg.iter() {
            if cdb[*cid].is_dead() {
                continue;
            }
            debug_assert!(!asg.locked(&cdb[*cid], *cid));
            #[cfg(feature = "incremental_solver")]
            {
                if !cdb[*cid].is(Flag::LEARNT) {
                    cdb.make_permanent_immortal(*cid);
                }
            }
            if cdb[*cid].is_dead() {
                dbg!(&cdb[*cid], pos.contains(cid));
                panic!("eliminate_var found a strange clause");
            }
            elim.remove_cid_occur(asg, *cid, &mut cdb[*cid]);
            // cdb.watches(*cid, "eliminate::elminate_var::148");
            cdb.remove_clause(*cid);
        }
        elim[vi].clear();
        asg.handle(SolverEvent::Eliminate(vi));
        rst.handle(SolverEvent::Eliminate(vi));
        elim.backward_subsumption_check(asg, cdb, timedout)
    }
}

/// returns `true` if elimination is impossible.
fn skip_var_elimination<A, C>(
    asg: &A,
    cdb: &C,
    pos: &[ClauseId],
    neg: &[ClauseId],
    v: VarId,
    eliminate_grow_limit: usize,
    eliminate_combination_limit: usize,
) -> bool
where
    A: AssignIF,
    C: ClauseDBIF,
{
    // avoid thrashing
    let limit = match cdb.check_size() {
        Ok(true) => eliminate_grow_limit,
        Ok(false) => eliminate_grow_limit / 4,
        Err(_) => return true,
    };
    let clslen = pos.len() + neg.len();
    let mut cnt = 0;
    for c_pos in pos {
        for c_neg in neg {
            let (res, clause_size) = check_to_merge(asg, cdb, *c_pos, *c_neg, v);
            if res {
                cnt += 1;
                if clslen + limit < cnt
                    || (eliminate_combination_limit != 0
                        && eliminate_combination_limit < clause_size)
                {
                    return true;
                }
            }
        }
    }
    false
}

/// Returns (enable-to-merge, the-size-of-clause-being-generated)
/// - `(false, -)` if one of the clauses is always satisfied.
/// - `(true, n)` if they are merge-able to a n-literal clause.
fn check_to_merge<A, C>(asg: &A, cdb: &C, cp: ClauseId, cq: ClauseId, vi: VarId) -> (bool, usize)
where
    A: AssignIF,
    C: ClauseDBIF,
{
    let c_p = &cdb[cp];
    let c_q = &cdb[cq];
    let mut cond_p: Option<Lit> = None;
    let mut cond_q: Option<Lit> = None;
    let mut count = 0;

    'next_lit: for lit in c_p.iter() {
        if lit.vi() == vi {
            cond_p = Some(*lit);
            continue;
        }
        if asg.var(lit.vi()).is(Flag::ELIMINATED) {
            continue;
        }
        // if this is the last occurrence of this literal, count it.
        for l in c_q.iter() {
            if !*lit == *l {
                return (true, 0);
            } else if *lit == *l {
                continue 'next_lit;
            }
        }
        count += 1;
    }
    for lit in c_q.iter() {
        if lit.vi() == vi {
            cond_q = Some(*lit);
            continue;
        }
        if asg.var(lit.vi()).is(Flag::ELIMINATED) {
            continue;
        }
        count += 1;
    }
    assert!(
        cond_p.map_or(false, |l0| cond_q.map_or(false, |l1| l0 == !l1)),
        "{}-mergable? {}:\n{:?}\n{:?}\n{:?}\n{:?}",
        vi,
        count,
        cond_p,
        c_p,
        cond_q,
        c_q
    );
    (
        cond_p.map_or(false, |l0| cond_q.map_or(false, |l1| l0 == !l1)),
        count,
    )
}

/// Return the real length of the generated clause by merging two clauses.
/// Return **zero** if one of the clauses is always satisfied. (merge_vec should not be used.)
fn merge<C>(cdb: &mut C, cip: ClauseId, ciq: ClauseId, v: VarId, vec: &mut Vec<Lit>) -> usize
where
    C: ClauseDBIF,
{
    vec.clear();
    let pqb = &cdb[cip];
    let qpb = &cdb[ciq];
    let ps_smallest = pqb.len() < qpb.len();
    let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
    #[cfg(feature = "trace_elimination")]
    println!("# merge {} & {}", pb, qb);
    'next_literal: for l in qb.iter() {
        if l.vi() != v {
            for j in pb.iter() {
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
    for l in pb.iter() {
        if l.vi() != v {
            vec.push(*l);
        }
    }
    #[cfg(feature = "trace_elimination")]
    println!(
        " - merge generated {:?} from {} and {} to eliminate {}",
        vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>(),
        pb,
        qb,
        v
    );
    vec.len()
}

fn make_eliminated_clauses<C>(
    cdb: &mut C,
    tmp: &mut Vec<Lit>,
    v: VarId,
    pos: &[ClauseId],
    neg: &[ClauseId],
) where
    C: ClauseDBIF,
{
    if neg.len() < pos.len() {
        for cid in neg {
            debug_assert!(!cdb[*cid].is_dead());
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from((v, true)));
    } else {
        for cid in pos {
            debug_assert!(!cdb[*cid].is_dead());
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from((v, false)));
    }
}

fn make_eliminating_unit_clause(vec: &mut Vec<Lit>, x: Lit) {
    #[cfg(feature = "trace_elimination")]
    println!(" - eliminator save {}", x);
    vec.push(x);
    vec.push(Lit::from(1usize));
}

fn make_eliminated_clause<C>(cdb: &mut C, vec: &mut Vec<Lit>, vi: VarId, cid: ClauseId)
where
    C: ClauseDBIF,
{
    let first = vec.len();
    // Copy clause to the vector. Remember the position where the variable 'v' occurs:
    let c = &cdb[cid];
    debug_assert!(!c.is_empty());
    for l in c.iter() {
        vec.push(*l);
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
    #[cfg(feature = "trace_elimination")]
    println!("# make_eliminated_clause: eliminate({}) clause {}", vi, c);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        assign::VarManipulateIF,
        cdb::{Clause, ClauseDB},
        processor::EliminateIF,
        solver::Solver,
    };
    use std::convert::TryFrom;

    impl Clause {
        #[allow(dead_code)]
        fn as_vec(&self) -> Vec<i32> {
            self.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
        }
    }
    impl ClauseDB {
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
            ref mut elim,
            ref mut rst,
            ref mut state,
            ..
        } = Solver::try_from("cnfs/uf8.cnf").expect("failed to load");
        let mut timedout = 10_000;
        let vi = 4;

        elim.activate();
        elim.prepare(asg, cdb, true);
        eliminate_var(asg, cdb, elim, rst, state, vi, &mut timedout).expect("panic");
        assert!(asg.var(vi).is(Flag::ELIMINATED));
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

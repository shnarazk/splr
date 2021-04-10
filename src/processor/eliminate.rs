/// Crate `eliminator` implements clause subsumption and var elimination.
use {
    super::{EliminateIF, Eliminator},
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
    let w = &mut elim[vi];
    if asg.assign(vi).is_some() || w.aborted {
        return Ok(());
    }
    debug_assert!(!v.is(Flag::ELIMINATED));
    // count only alive clauses
    w.pos_occurs.retain(|&c| !cdb[c].is(Flag::DEAD));
    w.neg_occurs.retain(|&c| !cdb[c].is(Flag::DEAD));
    let pos = &w.pos_occurs as *const Vec<ClauseId>;
    let neg = &w.neg_occurs as *const Vec<ClauseId>;
    unsafe {
        if *timedout < (*pos).len() * (*neg).len()
            || skip_var_elimination(asg, cdb, elim, &*pos, &*neg, vi)
        {
            return Ok(());
        } else {
            *timedout -= (*pos).len() * (*neg).len();
        }
        #[cfg(feature = "trace_elimination")]
        println!("# eliminate_var {}", vi);
        // OK, eliminate the literal and build constraints on it.
        make_eliminated_clauses(cdb, elim, vi, &*pos, &*neg);
        let vec = &mut state.new_learnt as *mut Vec<Lit>;
        // println!("eliminate_var {}: |p|: {} and |n|: {}", vi, (*pos).len(), (*neg).len());
        // Produce clauses in cross product:
        for p in &*pos {
            for n in &*neg {
                match merge(cdb, *p, *n, vi, &mut *vec) {
                    0 => {
                        #[cfg(feature = "trace_elimination")]
                        println!(
                            " - eliminate_var {}: fusion {}{} and {}{}",
                            vi, p, cdb[*p], n, cdb[*n],
                        );
                    }
                    1 => {
                        let lit = (*vec)[0];
                        #[cfg(feature = "trace_elimination")]
                        println!(
                            " - eliminate_var {}: found assign {} from {}{} and {}{}",
                            vi, lit, p, cdb[*p], n, cdb[*n],
                        );
                        match asg.assigned(lit) {
                            Some(true) => (),
                            Some(false) => return Err(SolverError::Inconsistent),
                            None => asg.assign_at_root_level(lit)?,
                        }
                        cdb.certificate_add_assertion(lit);
                    }
                    2 => {
                        if !cdb.registered_bin_clause((*vec)[0], (*vec)[1]) {
                            let cid = cdb.new_clause(
                                asg,
                                &mut *vec,
                                cdb[*p].is(Flag::LEARNT) && cdb[*n].is(Flag::LEARNT),
                                true,
                            );
                            elim.add_cid_occur(asg, cid, &mut cdb[cid], true);
                            #[cfg(feature = "trace_elimination")]
                            println!(
                                " - eliminate_var {}: X {} from {} and {}",
                                vi, cdb[cid], cdb[*p], cdb[*n],
                            );
                        }
                    }
                    _ => {
                        let cid = cdb.new_clause(
                            asg,
                            &mut *vec,
                            cdb[*p].is(Flag::LEARNT) && cdb[*n].is(Flag::LEARNT),
                            true,
                        );
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
        //
        //## VAR ELIMINATION
        //
        for cid in &*pos {
            debug_assert!(!asg.locked(&cdb[*cid], *cid));
            #[cfg(feature = "incremental_solver")]
            {
                if !cdb[*cid].is(Flag::LEARNT) {
                    cdb.make_permanent_immortal(*cid);
                }
            }
            cdb.detach(*cid);
            elim.remove_cid_occur(asg, *cid, &mut cdb[*cid]);
        }
        for cid in &*neg {
            debug_assert!(!asg.locked(&cdb[*cid], *cid));
            #[cfg(feature = "incremental_solver")]
            {
                if !cdb[*cid].is(Flag::LEARNT) {
                    cdb.make_permanent_immortal(*cid);
                }
            }
            cdb.detach(*cid);
            elim.remove_cid_occur(asg, *cid, &mut cdb[*cid]);
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
    elim: &Eliminator,
    pos: &[ClauseId],
    neg: &[ClauseId],
    v: VarId,
) -> bool
where
    A: AssignIF,
    C: ClauseDBIF,
{
    // avoid thrashing
    let limit = match cdb.check_size() {
        Ok(true) => elim.eliminate_grow_limit,
        Ok(false) => elim.eliminate_grow_limit / 4,
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

/// Returns:
/// - `(false, -)` if one of the clauses is always satisfied.
/// - `(true, n)` if they are merge-able to a n-literal clause.
fn check_to_merge<A, C>(asg: &A, cdb: &C, cp: ClauseId, cq: ClauseId, v: VarId) -> (bool, usize)
where
    A: AssignIF,
    C: ClauseDBIF,
{
    let pqb = &cdb[cp];
    let qpb = &cdb[cq];
    let ps_smallest = pqb.len() < qpb.len();
    let (pb, qb) = if ps_smallest { (pqb, qpb) } else { (qpb, pqb) };
    let mut size = pb.lits.len() + 1;
    'next_literal: for l in &qb.lits {
        if asg.var(l.vi()).is(Flag::ELIMINATED) {
            continue;
        }
        if l.vi() != v {
            for j in &pb.lits {
                if asg.var(j.vi()).is(Flag::ELIMINATED) {
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
    elim: &mut Eliminator,
    v: VarId,
    pos: &[ClauseId],
    neg: &[ClauseId],
) where
    C: ClauseDBIF,
{
    let tmp = &mut elim.elim_lits;
    if neg.len() < pos.len() {
        for cid in neg {
            debug_assert!(!cdb[*cid].is(Flag::DEAD));
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from_assign(v, true));
    } else {
        for cid in pos {
            debug_assert!(!cdb[*cid].is(Flag::DEAD));
            make_eliminated_clause(cdb, tmp, v, *cid);
        }
        make_eliminating_unit_clause(tmp, Lit::from_assign(v, false));
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
    for l in &c.lits {
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
    cdb.touch_var(vi);
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
            self.lits.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
        }
    }
    impl ClauseDB {
        #[allow(dead_code)]
        fn as_vec(&self) -> Vec<Vec<i32>> {
            self.iter()
                .skip(1)
                .filter(|c| !c.is(Flag::DEAD))
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
        cdb.garbage_collect();
        assert!(asg.var(vi).is(Flag::ELIMINATED));
        assert!(cdb
            .iter()
            .skip(1)
            .filter(|c| c.is(Flag::DEAD))
            .all(|c| c.is_empty()));
        assert!(cdb
            .iter()
            .skip(1)
            .all(|c| !c.lits.contains(&Lit::from_assign(vi, false))
                && !c.lits.contains(&Lit::from_assign(vi, false))));
    }
}

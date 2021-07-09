/// Crate `eliminator` implements clause subsumption and var elimination.
use {
    super::{EliminateIF, Eliminator},
    crate::{assign::AssignIF, cdb::ClauseDBIF, types::*},
};

impl Eliminator {
    pub fn try_subsume<A, C>(
        &mut self,
        asg: &mut A,
        cdb: &mut C,
        cid: ClauseId,
        did: ClauseId,
    ) -> MaybeInconsistent
    where
        A: AssignIF,
        C: ClauseDBIF,
    {
        match have_subsuming_lit(cdb, cid, did) {
            Some(NULL_LIT) => {
                #[cfg(feature = "trace_elimination")]
                println!(
                    "BackSubsC    => {} {} subsumed completely by {} {:#}",
                    did, cdb[did], cid, cdb[cid],
                );
                assert!(!cdb[did].is_dead());
                if !cdb[did].is(Flag::LEARNT) {
                    cdb[cid].turn_off(Flag::LEARNT);
                }
                self.remove_cid_occur(asg, did, &mut cdb[did]);
                cdb.remove_clause(did);
                self.num_subsumed += 1;
            }
            // To avoid making a big clause, we have to add a condition for combining them.
            Some(l) if cid.is_lifted_lit() => {
                #[cfg(feature = "trace_elimination")]
                println!("BackSubC subsumes {} from {} and {}", l, cid, did);
                strengthen_clause(asg, cdb, self, did, !l)?;
                self.enqueue_var(asg, l.vi(), true);
            }
            _ => (),
        }
        Ok(())
    }
}

/// returns a literal if these clauses can be merged by the literal.
fn have_subsuming_lit<C>(cdb: &mut C, cid: ClauseId, other: ClauseId) -> Option<Lit>
where
    C: ClauseDBIF,
{
    debug_assert!(!other.is_lifted_lit());
    if cid.is_lifted_lit() {
        let l = Lit::from(cid);
        let oh = &cdb[other];
        for lo in oh.iter() {
            if l == !*lo {
                return Some(l);
            }
        }
        return None;
    }
    let mut ret: Lit = NULL_LIT;
    let ch = &cdb[cid];
    debug_assert!(1 < ch.len());
    let ob = &cdb[other];
    debug_assert!(1 < ob.len());
    debug_assert!(ob.contains(ob[0]));
    debug_assert!(ob.contains(ob[1]));
    'next: for l in ch.iter() {
        for lo in ob.iter() {
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

/// removes `l` from clause `cid`
/// - calls `enqueue_clause`
/// - calls `enqueue_var`
fn strengthen_clause<A, C>(
    asg: &mut A,
    cdb: &mut C,
    elim: &mut Eliminator,
    cid: ClauseId,
    l: Lit,
) -> MaybeInconsistent
where
    A: AssignIF,
    C: ClauseDBIF,
{
    debug_assert!(!cdb[cid].is_dead());
    debug_assert!(1 < cdb[cid].len());
    match cdb.transform_by_elimination(cid, l) {
        RefClause::Clause(_) => {
            #[cfg(feature = "trace_elimination")]
            println!("cid {} drops literal {}", cid, l);

            elim.enqueue_clause(cid, &mut cdb[cid]);
            elim.remove_lit_occur(asg, l, cid);
            Ok(())
        }
        RefClause::Dead => panic!("impossible"),
        RefClause::EmptyClause => panic!("impossible"),
        RefClause::RegisteredClause(_) => {
            elim.remove_cid_occur(asg, cid, &mut cdb[cid]);
            cdb.remove_clause(cid);
            Ok(())
        }
        RefClause::UnitClause(l0) => {
            cdb.certificate_add_assertion(l0);
            elim.remove_cid_occur(asg, cid, &mut cdb[cid]);
            cdb.remove_clause(cid);
            match asg.assigned(l0) {
                None => asg.assign_at_root_level(l0),
                Some(true) => Ok(()),
                Some(false) => Err(SolverError::RootLevelConflict(Some(cid))),
            }
        }
    }
}

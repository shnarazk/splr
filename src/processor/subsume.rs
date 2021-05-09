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
                if !cdb[did].is(Flag::LEARNT) {
                    cdb[cid].turn_off(Flag::LEARNT);
                }
                assert!(!cdb[did].is_dead());
                self.remove_cid_occur(asg, did, &mut cdb[did]);
                // cdb.watches(did, "subsume35");
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
    debug_assert!(!cid.is_none());

    // | assert!(asg.assigned(cdb[cid].lit0()) != Some(false) && asg.assigned(cdb[cid].lit1()) != Some(false),
    // |         "{:?} - {:?}",
    // |         &cdb[cid],
    // |         cdb[cid].iter().map(|l| asg.assigned(*l)).collect::<Vec<_>>(),
    // | );
    match cdb.transform_by_elimination(cid, l) {
        RefClause::BiClause | RefClause::Clause => {
            #[cfg(feature = "trace_elimination")]
            println!("cid {} drops literal {}", cid, l);

            elim.enqueue_clause(cid, &mut cdb[cid]);
            elim.remove_lit_occur(asg, l, cid);
            Ok(())
        }
        RefClause::Dead => panic!("impossible"),
        RefClause::EmptyClause => panic!("imossible"),
        RefClause::RegisteredBiClause(_) => {
            elim.remove_cid_occur(asg, cid, &mut cdb[cid]);
            // cdb.watches(cid, "subsume133");
            cdb.remove_clause(cid);
            Ok(())
        }
        RefClause::UnitClause(l0) => {
            // Vaporize the binary clause
            // debug_assert!(2 == cdb[cid].len());
            // let c0 = cdb[cid][0];
            // debug_assert_ne!(c0, l);

            #[cfg(feature = "trace_elimination")]
            println!(
                "{} {:?} is removed and its first literal {} is enqueued.",
                cid, cdb[cid], l0,
            );

            cdb.certificate_add_assertion(l0);
            elim.remove_cid_occur(asg, cid, &mut cdb[cid]);
            // cdb.watches(cid, "subsume127");
            cdb.remove_clause(cid);
            asg.assign_at_root_level(l0)
        }
    }
}

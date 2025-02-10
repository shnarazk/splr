/// Module `eliminator` implements clause subsumption and var elimination.
use {
    super::{EliminateIF, Eliminator},
    crate::{
        assign::{AssignStack, PropagateIF},
        cdb::{ClauseDB, ClauseDBIF},
        types::*,
    },
};

#[derive(Clone, Eq, Debug, Ord, PartialEq, PartialOrd)]
enum Subsumable {
    None,
    By(BSVR),
    Success,
}

impl Eliminator {
    pub fn try_subsume(
        &mut self,
        asg: &mut AssignStack,
        cdb: &mut ClauseDB,
        cid: ClauseId,
        did: ClauseId,
    ) -> MaybeInconsistent {
        match have_subsuming_lit(cdb, cid, did) {
            Subsumable::Success => {
                #[cfg(feature = "trace_elimination")]
                println!(
                    "BackSubsC    => {} {} subsumed completely by {} {:#}",
                    did, cdb[did], cid, cdb[cid],
                );
                debug_assert!(!cdb[did].is_dead());
                if !cdb[did].is(FlagClause::LEARNT) {
                    cdb[cid].turn_off(FlagClause::LEARNT);
                }
                self.remove_cid_occur(did, &mut cdb[did]);
                cdb.remove_clause(did);
                self.num_subsumed += 1;
            }
            // To avoid making a big clause, we have to add a condition for combining them.
            Subsumable::By(l) => {
                debug_assert!(cid.is_lifted_lit());
                #[cfg(feature = "trace_elimination")]
                println!("BackSubC subsumes {} from {} and {}", l, cid, did);
                strengthen_clause(asg, cdb, self, did, !l)?;
                self.enqueue_var(l.vi(), true);
            }
            Subsumable::None => (),
        }
        Ok(())
    }
}

/// returns a literal if these clauses can be merged by the literal.
fn have_subsuming_lit(cdb: &mut ClauseDB, cid: ClauseId, other: ClauseId) -> Subsumable {
    debug_assert!(!other.is_lifted_lit());
    if cid.is_lifted_lit() {
        let l = BSVR::from(cid);
        let oh = &cdb[other];
        for lo in oh.iter() {
            if l == !*lo {
                return Subsumable::By(l);
            }
        }
        return Subsumable::None;
    }
    // let mut ret: Subsumable = Subsumable::Success;
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
                // } else if ret == Subsumable::Success && *l == !*lo {
                //     ret = Subsumable::By(*l);
                //     continue 'next;
            }
        }
        return Subsumable::None;
    }
    Subsumable::Success
}

/// removes `l` from clause `cid`
/// - calls `enqueue_clause`
/// - calls `enqueue_var`
fn strengthen_clause(
    asg: &mut AssignStack,
    cdb: &mut ClauseDB,
    elim: &mut Eliminator,
    cid: ClauseId,
    l: BSVR,
) -> MaybeInconsistent {
    debug_assert!(!cdb[cid].is_dead());
    debug_assert!(1 < cdb[cid].len());
    match cdb.transform_by_elimination(cid, l) {
        RefClause::Clause(_ci) => {
            #[cfg(feature = "trace_elimination")]
            println!("cid {} drops literal {}", cid, l);

            elim.enqueue_clause(cid, &mut cdb[cid]);
            elim.remove_lit_occur(l, cid);
            Ok(())
        }
        RefClause::RegisteredClause(_) => {
            elim.remove_cid_occur(cid, &mut cdb[cid]);
            cdb.remove_clause(cid);
            Ok(())
        }
        RefClause::UnitClause(l0) => {
            cdb.certificate_add_assertion(Lit::from(l0));
            elim.remove_cid_occur(cid, &mut cdb[cid]);
            cdb.remove_clause(cid);
            match l0.lit_assigned() {
                None => asg.assign_at_root_level(l0),
                Some(true) => Ok(()),
                Some(false) => Err(SolverError::RootLevelConflict((l0, l0.var.reason))),
            }
        }
        RefClause::Dead | RefClause::EmptyClause => unreachable!("strengthen_clause"),
    }
}

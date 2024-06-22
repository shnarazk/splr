/// Module `eliminator` implements clause subsumption and var elimination.
use {
    super::{EliminateIF, Eliminator},
    crate::{
        assign::AssignIF,
        cdb::{ClauseDBIF, LiftedClauseIF},
        types::*,
    },
    std::collections::HashSet,
};

#[cfg(feature = "deterministic")]
use ahash::RandomState;

#[derive(Clone, Eq, Debug, Ord, PartialEq, PartialOrd)]
enum Subsumable {
    None,
    By(Lit),
    Success,
}

impl Eliminator {
    pub fn try_subsume(
        &mut self,
        asg: &mut impl AssignIF,
        cdb: &mut impl ClauseDBIF,
        ci: ClauseIndex,
        di: ClauseIndex,
        #[cfg(feature = "deterministic")] deads: &mut HashSet<Lit, RandomState>,
        #[cfg(not(feature = "deterministic"))] deads: &mut HashSet<Lit>,
    ) -> MaybeInconsistent {
        match have_subsuming_lit(cdb, ci, di) {
            Subsumable::Success => {
                #[cfg(feature = "trace_elimination")]
                println!(
                    "BackSubsC    => {} {} subsumed completely by {} {:#}",
                    di, cdb[di], ci, cdb[ci],
                );
                debug_assert!(!cdb[di].is_dead());
                if !cdb[di].is(FlagClause::LEARNT) {
                    cdb[ci].turn_off(FlagClause::LEARNT);
                }
                self.remove_cid_occur(asg, di, &mut cdb[di]);
                cdb.nullify_clause(di, deads);
                self.num_subsumed += 1;
            }
            // To avoid making a big clause, we have to add a condition for combining them.
            Subsumable::By(l) => {
                debug_assert!(ci.is_lifted());
                #[cfg(feature = "trace_elimination")]
                println!("BackSubC subsumes {} from {} and {}", l, ci, di);
                strengthen_clause(asg, cdb, self, di, !l, deads)?;
                self.enqueue_var(asg, l.vi(), true);
            }
            Subsumable::None => (),
        }
        Ok(())
    }
}

/// returns a literal if these clauses can be merged by the literal.
fn have_subsuming_lit(
    cdb: &mut impl ClauseDBIF,
    ci: ClauseIndex,
    other: ClauseIndex,
) -> Subsumable {
    debug_assert!(!other.is_lifted());
    if ci.is_lifted() {
        let l = ci.unlift();
        let oh = &cdb[other];
        for lo in oh.iter() {
            if l == !*lo {
                return Subsumable::By(l);
            }
        }
        return Subsumable::None;
    }
    // let mut ret: Subsumable = Subsumable::Success;
    let ch = &cdb[ci];
    debug_assert!(1 < ch.len());
    let ob = &cdb[other];
    debug_assert!(1 < ob.len());
    // debug_assert!(ob.contains(ob[0]));
    // debug_assert!(ob.contains(ob[1]));
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
    asg: &mut impl AssignIF,
    cdb: &mut impl ClauseDBIF,
    elim: &mut Eliminator,
    ci: ClauseIndex,
    l: Lit,
    #[cfg(feature = "deterministic")] deads: &mut HashSet<Lit, RandomState>,
    #[cfg(not(feature = "deterministic"))] deads: &mut HashSet<Lit>,
) -> MaybeInconsistent {
    debug_assert!(!cdb[ci].is_dead());
    debug_assert!(1 < cdb[ci].len());
    match cdb.transform_by_elimination(ci, l) {
        RefClause::Clause(_ci) => {
            #[cfg(feature = "trace_elimination")]
            println!("ci {} drops literal {}", ci, l);

            elim.enqueue_clause(ci, &mut cdb[ci]);
            elim.remove_lit_occur(asg, l, ci);
            Ok(())
        }
        RefClause::RegisteredClause(_) => {
            elim.remove_cid_occur(asg, ci, &mut cdb[ci]);
            cdb.nullify_clause(ci, deads);
            Ok(())
        }
        RefClause::UnitClause(l0) => {
            cdb.certificate_add_assertion(l0);
            elim.remove_cid_occur(asg, ci, &mut cdb[ci]);
            cdb.nullify_clause(ci, deads);
            match asg.assigned(l0) {
                None => asg.assign_at_root_level(l0),
                Some(true) => Ok(()),
                Some(false) => Err(SolverError::RootLevelConflict((l0, asg.reason(l0.vi())))),
            }
        }
        RefClause::Dead | RefClause::EmptyClause => unreachable!("strengthen_clause"),
    }
}

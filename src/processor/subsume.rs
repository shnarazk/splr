/// Module `eliminator` implements clause subsumption and var elimination.
use {
    super::{EliminateIF, Eliminator},
    crate::{assign::AssignIF, cdb::ClauseDBIF, types::*},
};

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
        mut cr: ClauseRef,
        mut dr: ClauseRef,
    ) -> MaybeInconsistent {
        match have_subsuming_lit(cdb, cr, dr) {
            Subsumable::Success => {
                #[cfg(feature = "trace_elimination")]
                println!(
                    "BackSubsC    => {} {} subsumed completely by {} {:#}",
                    dr, cdb[dr], cr, cdb[cr],
                );
                debug_assert!(!dr.get().is_dead());
                if !dr.get().is(FlagClause::LEARNT) {
                    cr.get().turn_off(FlagClause::LEARNT);
                }
                self.remove_cid_occur(asg, dr, &mut dr.get_mut());
                cdb.remove_clause(dr);
                self.num_subsumed += 1;
            }
            // To avoid making a big clause, we have to add a condition for combining them.
            Subsumable::By(l) => {
                debug_assert!(cr.is_lifted_lit());
                #[cfg(feature = "trace_elimination")]
                println!("BackSubC subsumes {} from {} and {}", l, cr, dr);
                strengthen_clause(asg, cdb, self, dr, !l)?;
                self.enqueue_var(asg, l.vi(), true);
            }
            Subsumable::None => (),
        }
        Ok(())
    }
}

/// returns a literal if these clauses can be merged by the literal.
fn have_subsuming_lit(cdb: &mut impl ClauseDBIF, cr: ClauseRef, other: ClauseRef) -> Subsumable {
    debug_assert!(!other.is_lifted_lit());
    if cr.is_lifted_lit() {
        let l = Lit::from(cr);
        let oh = other.get();
        for lo in oh.iter() {
            if l == !*lo {
                return Subsumable::By(l);
            }
        }
        return Subsumable::None;
    }
    // let mut ret: Subsumable = Subsumable::Success;
    let ch = cr.get();
    debug_assert!(1 < ch.len());
    let ob = other.get();
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
    asg: &mut impl AssignIF,
    cdb: &mut impl ClauseDBIF,
    elim: &mut Eliminator,
    mut cr: ClauseRef,
    l: Lit,
) -> MaybeInconsistent {
    let mut c = cr.get_mut();
    debug_assert!(!c.is_dead());
    debug_assert!(1 < c.len());
    match cdb.transform_by_elimination(cr, l) {
        RefClause::Clause(_ci) => {
            #[cfg(feature = "trace_elimination")]
            println!("cr {} drops literal {}", cr, l);

            elim.enqueue_clause(cr, &mut c);
            elim.remove_lit_occur(asg, l, cr);
            Ok(())
        }
        RefClause::RegisteredClause(_) => {
            elim.remove_cid_occur(asg, cr, &mut c);
            cdb.remove_clause(cr);
            Ok(())
        }
        RefClause::UnitClause(l0) => {
            cdb.certificate_add_assertion(l0);
            elim.remove_cid_occur(asg, cr, &mut c);
            cdb.remove_clause(cr);
            match asg.assigned(l0) {
                None => asg.assign_at_root_level(l0),
                Some(true) => Ok(()),
                Some(false) => Err(SolverError::RootLevelConflict((l0, asg.reason(l0.vi())))),
            }
        }
        RefClause::Dead | RefClause::EmptyClause => unreachable!("strengthen_clause"),
    }
}

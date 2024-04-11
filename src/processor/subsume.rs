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
        cr: ClauseRef,
        dr: ClauseRef,
    ) -> MaybeInconsistent {
        assert_ne!(cr, dr);
        let rcc = cr.get();
        let mut c = rcc.borrow_mut();
        // assert!(!c.is_dead());
        let rcd = dr.get();
        let mut d = rcd.borrow_mut();
        // assert!(!d.is_dead());
        // if !c.is(FlagClause::LEARNT) || !d.is(FlagClause::LEARNT) {
        //     return Ok(());
        // }
        // if !c.is(FlagClause::LEARNT) && !d.is(FlagClause::LEARNT) {
        //     return Ok(());
        // }
        match have_subsuming_lit(&cr, &c, &dr, &d) {
            Subsumable::Success => {
                #[cfg(feature = "trace_elimination")]
                println!("BackSubsC    => {:#} subsumed completely by {:#}", d, c);
                debug_assert!(!d.is_dead());
                if !d.is(FlagClause::LEARNT) {
                    c.turn_off(FlagClause::LEARNT);
                }
                self.remove_cid_occur(asg, dr.clone(), &mut d);
                drop(d);
                cdb.remove_clause(dr);
                self.num_subsumed += 1;
            }
            // To avoid making a big clause, we have to add a condition for combining them.
            Subsumable::By(l) => {
                debug_assert!(cr.is_lifted());
                #[cfg(feature = "trace_elimination")]
                println!("BackSubC subsumes {} from {:#} and {:#}", l, c, d);
                drop(d);
                strengthen_clause(asg, cdb, self, dr, !l)?;
                self.enqueue_var(asg, l.vi(), true);
            }
            Subsumable::None => (),
        }
        Ok(())
    }
}

/// returns a literal if these clauses can be merged by the literal.
fn have_subsuming_lit(cr: &ClauseRef, c: &Clause, other: &ClauseRef, o: &Clause) -> Subsumable {
    debug_assert!(!other.is_lifted());
    if cr.is_lifted() {
        let l = cr.unlift(c);
        for lo in o.iter() {
            if l == !*lo {
                return Subsumable::By(l);
            }
        }
        return Subsumable::None;
    }
    // let mut ret: Subsumable = Subsumable::Success;
    debug_assert!(1 < c.len());
    debug_assert!(1 < o.len());
    'next: for l in c.iter() {
        for lo in o.iter() {
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
    cr: ClauseRef,
    l: Lit,
) -> MaybeInconsistent {
    // let mut c = cr.get_mut();
    // debug_assert!(!c.is_dead());
    // debug_assert!(1 < c.len());
    match cdb.transform_by_elimination(cr.clone(), l) {
        RefClause::Clause(ci) => {
            #[cfg(feature = "trace_elimination")]
            println!("cr {} drops literal {}", cr, l);

            let rcc = ci.get();
            let mut c = rcc.borrow_mut();
            elim.enqueue_clause(cr.clone(), &mut c);
            elim.remove_lit_occur(asg, l, &cr);
            Ok(())
        }
        RefClause::RegisteredClause(ci) => {
            let rcc = ci.get();
            let mut c = rcc.borrow_mut();
            elim.remove_cid_occur(asg, cr.clone(), &mut c);
            drop(c);
            cdb.remove_clause(cr.clone());
            Ok(())
        }
        RefClause::UnitClause(l0) => {
            let rcc = cr.get();
            let mut c = rcc.borrow_mut();
            cdb.certificate_add_assertion(l0);
            elim.remove_cid_occur(asg, cr.clone(), &mut c);
            drop(c);
            cdb.remove_clause(cr.clone());
            match asg.assigned(l0) {
                None => asg.assign_at_root_level(l0),
                Some(true) => Ok(()),
                Some(false) => Err(SolverError::RootLevelConflict((
                    l0,
                    asg.reason(l0.vi()).clone(),
                ))),
            }
        }
        RefClause::Dead | RefClause::EmptyClause => unreachable!("strengthen_clause"),
    }
}

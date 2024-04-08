/// Module `eliminator` implements clause subsumption and var elimination.
use {
    super::{EliminateIF, Eliminator},
    crate::{
        assign::AssignIF,
        cdb::{ClauseDBIF, LiftedClauseIdIF},
        types::*,
    },
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
        cid: ClauseId,
        did: ClauseId,
    ) -> MaybeInconsistent {
        let rcc = cdb[cid];
        let mut c = rcc.borrow_mut();
        match have_subsuming_lit(cdb, cid, did) {
            Subsumable::Success => {
                #[cfg(feature = "trace_elimination")]
                println!(
                    "BackSubsC    => {} {} subsumed completely by {} {:#}",
                    did, cdb[did], cid, cdb[cid],
                );
                let rcd = cdb[did];
                let mut d = rcd.borrow_mut();
                debug_assert!(!d.is_dead());
                if !d.is(FlagClause::LEARNT) {
                    c.turn_off(FlagClause::LEARNT);
                }
                self.remove_cid_occur(asg, did, &mut d);
                cdb.remove_clause(did);
                self.num_subsumed += 1;
            }
            // To avoid making a big clause, we have to add a condition for combining them.
            Subsumable::By(l) => {
                debug_assert!(cid.is_lifted());
                #[cfg(feature = "trace_elimination")]
                println!("BackSubC subsumes {} from {} and {}", l, cid, did);
                strengthen_clause(asg, cdb, self, did, !l)?;
                self.enqueue_var(asg, l.vi(), true);
            }
            Subsumable::None => (),
        }
        Ok(())
    }
}

/// returns a literal if these clauses can be merged by the literal.
fn have_subsuming_lit(cdb: &mut impl ClauseDBIF, cid: ClauseId, other: ClauseId) -> Subsumable {
    debug_assert!(!other.is_lifted());
    if cid.is_lifted() {
        let l = cid.unlift();
        let roh = &cdb[other];
        let oh = roh.borrow();
        for lo in oh.iter() {
            if l == !*lo {
                return Subsumable::By(l);
            }
        }
        return Subsumable::None;
    }
    // let mut ret: Subsumable = Subsumable::Success;
    let rch = cdb[cid];
    let ch = rch.borrow();
    debug_assert!(1 < ch.len());
    let rob = &cdb[other];
    let ob = rob.borrow();
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
    cid: ClauseId,
    l: Lit,
) -> MaybeInconsistent {
    let rcc = cdb[cid];
    let mut c = rcc.borrow_mut();
    debug_assert!(!c.is_dead());
    debug_assert!(1 < c.len());
    match cdb.transform_by_elimination(cid, l) {
        RefClause::Clause(_ci) => {
            #[cfg(feature = "trace_elimination")]
            println!("cid {} drops literal {}", cid, l);

            elim.enqueue_clause(cid, &mut c);
            elim.remove_lit_occur(asg, l, cid);
            Ok(())
        }
        RefClause::RegisteredClause(_) => {
            elim.remove_cid_occur(asg, cid, &mut c);
            cdb.remove_clause(cid);
            Ok(())
        }
        RefClause::UnitClause(l0) => {
            cdb.certificate_add_assertion(l0);
            let rcc = cdb[cid];
            let mut c = rcc.borrow_mut();
            elim.remove_cid_occur(asg, cid, &mut c);
            cdb.remove_clause(cid);
            match asg.assigned(l0) {
                None => asg.assign_at_root_level(l0),
                Some(true) => Ok(()),
                Some(false) => Err(SolverError::RootLevelConflict((l0, asg.reason(l0.vi())))),
            }
        }
        RefClause::Dead | RefClause::EmptyClause => unreachable!("strengthen_clause"),
    }
}

use {
    super::{
        binary::BinaryLinkIF, dlink::LinkHead, ema::ProgressLBD, BinaryLinkDB, CertificationStore,
        Clause,
    },
    crate::types::*,
    std::ops::{Index, IndexMut},
};

/// Clause database
///
///```
/// use crate::{splr::config::Config, splr::types::*};
/// use crate::splr::cdb::ClauseDB;
/// let cdb = ClauseDB::instantiate(&Config::default(), &CNFDescription::default());
///```
#[derive(Clone, Debug)]
pub struct ClauseDB {
    /// container of clauses
    pub(super) clause: Vec<Clause>,
    /// hashed representation of binary clauses.
    ///## Note
    /// This means a biclause \[l0, l1\] is stored at bi_clause\[l0\] instead of bi_clause\[!l0\].
    ///
    pub(super) binary_link: BinaryLinkDB,
    /// container of watch literals
    pub(super) watch: Vec<LinkHead>,
    /// see unsat_certificate.rs
    pub(super) certification_store: CertificationStore,
    /// a number of clauses to emit out-of-memory exception
    pub(super) soft_limit: usize,
    /// 'small' clause threshold
    pub(super) co_lbd_bound: u16,
    // not in use
    // lbd_frozen_clause: usize,

    // bi-clause completion
    pub(super) bi_clause_completion_queue: Vec<Lit>,
    pub(super) num_bi_clause_completion: usize,

    //
    //## clause rewarding
    //
    /// an index for counting elapsed time
    #[cfg(feature = "clause_rewarding")]
    pub(super) tick: usize,
    #[cfg(feature = "clause_rewarding")]
    pub(super) activity_decay: f64,
    #[cfg(feature = "clause_rewarding")]
    pub(super) activity_anti_decay: f64,

    //
    //## LBD
    //
    /// a working buffer for LBD calculation
    pub(super) lbd_temp: Vec<usize>,
    pub(super) lbd: ProgressLBD,

    //
    //## statistics
    //
    /// the number of active (not DEAD) clauses.
    pub(super) num_clause: usize,
    /// the number of binary clauses.
    pub(super) num_bi_clause: usize,
    /// the number of binary learnt clauses.
    pub(super) num_bi_learnt: usize,
    /// the number of clauses which LBDs are 2.
    pub(super) num_lbd2: usize,
    /// the present number of learnt clauses.
    pub(super) num_learnt: usize,
    /// the number of reductions.
    pub(super) num_reduction: usize,
    /// the number of reregistration of a bi-clause
    pub(super) num_reregistration: usize,
    /// Literal Block Entanglement
    /// EMA of LBD of clauses used in conflict analysis (dependency graph)
    pub(super) lb_entanglement: Ema2,
    /// cutoff value used in the last `reduce`
    pub(super) reduction_threshold: f64,

    //
    //## incremental solving
    //
    pub(super) eliminated_permanent: Vec<Vec<Lit>>,
}

// impl Index<Lit> for ClauseDB {
//     type Output = Clause;
//     #[inline]
//     fn index(&self, lit: Lit) -> &Self::Output {
//         &self.clause[ClauseIndex::from(lit)]
//     }
// }

// impl IndexMut<Lit> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, lit: Lit) -> &mut Self::Output {
//         &mut self.clause[ClauseIndex::from(lit)]
//     }
// }

impl Index<ClauseIndex> for ClauseDB {
    type Output = Clause;
    #[inline]
    fn index(&self, ci: ClauseIndex) -> &Clause {
        if cfg!(feature = "unsafe_access") {
            unsafe { self.clause.get_unchecked(ci) }
        } else {
            &self.clause[ci]
        }
    }
}

impl IndexMut<ClauseIndex> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, ci: ClauseIndex) -> &mut Clause {
        if cfg!(feature = "unsafe_access") {
            unsafe { self.clause.get_unchecked_mut(ci) }
        } else {
            &mut self.clause[ci]
        }
    }
}

// impl Index<&ClauseId> for ClauseDB {
//     type Output = Clause;
//     #[inline]
//     fn index(&self, cid: &ClauseId) -> &Clause {
//         let i = NonZeroU32::get(cid.ordinal) as usize;
//         if cfg!(feature = "unsafe_access") {
//             unsafe { self.clause.get_unchecked(i) }
//         } else {
//             &self.clause[i]
//         }
//     }
// }

// impl IndexMut<&ClauseId> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, cid: &ClauseId) -> &mut Clause {
//         let i = NonZeroU32::get(cid.ordinal) as usize;
//         if cfg!(feature = "unsafe_access") {
//             unsafe { self.clause.get_unchecked_mut(i) }
//         } else {
//             &mut self.clause[i]
//         }
//     }
// }

// impl Index<Range<usize>> for ClauseDB {
//     type Output = [Clause];
//     #[inline]
//     fn index(&self, r: Range<usize>) -> &[Clause] {
//         if cfg!(feature = "unsafe_access") {
//             unsafe { self.clause.get_unchecked(r) }
//         } else {
//             &self.clause[r]
//         }
//     }
// }

// impl Index<RangeFrom<usize>> for ClauseDB {
//     type Output = [Clause];
//     #[inline]
//     fn index(&self, r: RangeFrom<usize>) -> &[Clause] {
//         if cfg!(feature = "unsafe_access") {
//             unsafe { self.clause.get_unchecked(r) }
//         } else {
//             &self.clause[r]
//         }
//     }
// }

// impl IndexMut<Range<usize>> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, r: Range<usize>) -> &mut [Clause] {
//         if cfg!(feature = "unsafe_access") {
//             unsafe { self.clause.get_unchecked_mut(r) }
//         } else {
//             &mut self.clause[r]
//         }
//     }
// }

// impl IndexMut<RangeFrom<usize>> for ClauseDB {
//     #[inline]
//     fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Clause] {
//         if cfg!(feature = "unsafe_access") {
//             unsafe { self.clause.get_unchecked_mut(r) }
//         } else {
//             &mut self.clause[r]
//         }
//     }
// }

impl Instantiate for ClauseDB {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> ClauseDB {
        let nv = cnf.num_of_variables;
        let nc = cnf.num_of_clauses;
        ClauseDB {
            clause: vec![Clause::default(); 1 + nc], // ci 0 must refer to the header
            binary_link: BinaryLinkDB::instantiate(config, cnf),
            watch: vec![LinkHead::default(); 2 * (nv + 1)],
            certification_store: CertificationStore::instantiate(config, cnf),
            soft_limit: config.c_cls_lim,
            lbd: ProgressLBD::instantiate(config, cnf),

            #[cfg(feature = "clause_rewarding")]
            activity_decay: config.crw_dcy_rat,
            #[cfg(feature = "clause_rewarding")]
            activity_anti_decay: 1.0 - config.crw_dcy_rat,

            lbd_temp: vec![0; nv + 1],
            ..ClauseDB::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        #[allow(clippy::single_match)]
        match e {
            SolverEvent::Assert(_) => {
                self.lbd.update(0);
            }
            SolverEvent::NewVar => {
                self.binary_link.add_new_var();
                // for negated literal
                self.watch.push(LinkHead::default());
                // for positive literal
                self.watch.push(LinkHead::default());
                self.lbd_temp.push(0);
            }
            SolverEvent::Restart => {
                // self.lbd.reset_to(self.lb_entanglement.get());
                // self.lbd.reset_to(0.0);
            }
            _ => (),
        }
    }
}

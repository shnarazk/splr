//! main struct AssignStack
use {
    super::{ema::ProgressASG, PropagateIF},
    crate::{cdb::ClauseDB, types::*, vam::VarActivityManager, var_vector::*},
    std::{fmt, ops::Range, slice::Iter},
};

#[cfg(any(feature = "best_phases_tracking", feature = "rephase"))]
use {
    rustc_data_structures::fx::{FxHashMap, FxHasher},
    std::{collections::HashMap, hash::BuildHasherDefault},
};

#[cfg(feature = "trail_saving")]
use super::TrailSavingIF;

/// A record of assignment. It's called 'trail' in Glucose.
#[derive(Clone, Debug)]
pub struct AssignStack {
    /// record of assignment
    pub(super) trail: Vec<Lit>,
    pub(super) trail_lim: Vec<usize>,
    /// the-number-of-assigned-and-propagated-vars + 1
    pub(super) q_head: usize,
    pub(super) root_level: DecisionLevel,

    #[cfg(feature = "trail_saving")]
    pub(super) trail_saved: Vec<Lit>,

    pub(super) num_reconflict: usize,
    pub(super) num_repropagation: usize,

    //
    //## Phase handling
    //
    pub(super) best_assign: bool,
    pub(super) build_best_at: usize,
    pub(super) num_best_assign: usize,
    pub(super) num_rephase: usize,
    pub(super) bp_divergence_ema: Ema,

    #[cfg(feature = "best_phases_tracking")]
    pub(super) best_phases: FxHashMap<VarId, (bool, AssignReason)>,
    #[cfg(feature = "rephase")]
    pub(super) phase_age: usize,

    //
    //## Stage
    //
    pub(super) stage_scale: usize,

    //## Elimanated vars
    //
    pub eliminated: Vec<Lit>,

    //
    //## Statistics
    //
    /// the number of asserted vars.
    pub(super) num_asserted_vars: usize,
    /// the number of eliminated vars.
    pub(super) num_eliminated_vars: usize,
    pub(super) num_decisions: usize,
    pub(super) num_propagations: usize,
    pub(super) num_conflicts: usize,
    pub(super) num_restarts: usize,
    /// Assign rate EMA
    pub(super) assign_rate: ProgressASG,
    /// Decisions Per Conflict
    pub(super) dpc_ema: EmaSU,
    /// Propagations Per Conflict
    pub(super) ppc_ema: EmaSU,
    /// Conflicts Per Restart
    pub(super) cpr_ema: EmaSU,
}

impl Default for AssignStack {
    fn default() -> AssignStack {
        AssignStack {
            trail: Vec::new(),
            trail_lim: Vec::new(),
            q_head: 0,
            root_level: 0,

            #[cfg(feature = "trail_saving")]
            trail_saved: Vec::new(),

            num_reconflict: 0,
            num_repropagation: 0,

            best_assign: false,
            build_best_at: 0,
            num_best_assign: 0,
            num_rephase: 0,
            bp_divergence_ema: Ema::new(10),

            #[cfg(feature = "best_phases_tracking")]
            best_phases:
                HashMap::<VarId, (bool, AssignReason), BuildHasherDefault<FxHasher>>::default(),
            #[cfg(feature = "rephase")]
            phase_age: 0,

            stage_scale: 1,
            eliminated: Vec::new(),

            num_asserted_vars: 0,
            num_eliminated_vars: 0,
            num_decisions: 0,
            num_propagations: 0,
            num_conflicts: 0,
            num_restarts: 0,
            assign_rate: ProgressASG::default(),
            dpc_ema: EmaSU::new(100),
            ppc_ema: EmaSU::new(100),
            cpr_ema: EmaSU::new(100),
        }
    }
}

impl<'a> IntoIterator for &'a mut AssignStack {
    type Item = &'a Lit;
    type IntoIter = Iter<'a, Lit>;
    fn into_iter(self) -> Self::IntoIter {
        self.trail.iter()
    }
}

impl From<&mut AssignStack> for Vec<i32> {
    fn from(asg: &mut AssignStack) -> Vec<i32> {
        asg.trail.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
    }
}

impl Instantiate for AssignStack {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> AssignStack {
        let nv = cnf.num_of_variables;
        AssignStack {
            trail: Vec::with_capacity(nv),
            #[cfg(feature = "trail_saving")]
            trail_saved: Vec::with_capacity(nv),

            assign_rate: ProgressASG::instantiate(config, cnf),
            ..AssignStack::default()
        }
    }
    #[inline]
    fn handle(&mut self, e: SolverEvent) {
        match e {
            // called only by assertion on chronoBT
            // So execute everything of `assign_by_unitclause` but cancel_until(root_level)
            SolverEvent::Conflict => (),
            SolverEvent::Eliminate(vi) => {
                debug_assert_eq!(self.decision_level(), self.root_level());
                debug_assert!(self.trail.iter().all(|l| l.vi() != vi));
                self.num_eliminated_vars += 1;
            }
            SolverEvent::Stage(scale) => {
                self.stage_scale = scale;
                #[cfg(feature = "trail_saving")]
                self.clear_saved_trail();
            }
            SolverEvent::NewVar => {
                VarActivityManager::expand_heap();
            }
            SolverEvent::Reinitialize => {
                self.cancel_until(self.root_level);
                debug_assert_eq!(self.decision_level(), self.root_level);
                #[cfg(feature = "trail_saving")]
                self.clear_saved_trail();
                // self.num_eliminated_vars = self
                //     .var
                //     .iter()
                //     .filter(|v| v.is(FlagVar::ELIMINATED))
                //     .count();
            }
            e => panic!("don't call asg with {e:?}"),
        }
    }
}
impl AssignStack {
    /// return root level.
    pub fn root_level(&self) -> DecisionLevel {
        self.root_level
    }
    pub fn num_asserted_vars(&self) -> usize {
        self.num_asserted_vars
    }
    pub fn num_eliminated_vars(&self) -> usize {
        self.num_eliminated_vars
    }
    pub fn num_decisions(&self) -> usize {
        self.num_decisions
    }
    pub fn num_propagations(&self) -> usize {
        self.num_propagations
    }
    pub fn num_conflicts(&self) -> usize {
        self.num_conflicts
    }
    pub fn num_restart(&self) -> usize {
        self.num_restarts
    }
    pub fn num_unasserted_vars(&self) -> usize {
        VarRef::num_vars() - self.num_asserted_vars - self.num_eliminated_vars
    }
    pub fn num_unassigned_vars(&self) -> usize {
        VarRef::num_vars() - self.num_asserted_vars - self.num_eliminated_vars - self.trail.len()
    }
    pub fn num_unreachable_vars(&self) -> usize {
        VarRef::num_vars() - self.num_best_assign
    }
    pub fn assign_rate(&self) -> &EmaView {
        self.assign_rate.as_view()
    }
    /// EMA of Decision/Conflict
    pub fn dpc_ema(&self) -> &EmaView {
        self.dpc_ema.as_view()
    }
    /// EMA of Propagation/Conflict
    pub fn ppc_ema(&self) -> &EmaView {
        self.ppc_ema.as_view()
    }
    /// EMA of Conflict/Restart
    pub fn cpr_ema(&self) -> &EmaView {
        self.cpr_ema.as_view()
    }
    /// return the i-th element in the stack.
    pub fn stack(&self, i: usize) -> Lit {
        self.trail[i]
    }
    /// return literals in the range of stack.
    pub fn stack_range(&self, r: Range<usize>) -> &[Lit] {
        &self.trail[r]
    }
    /// return the number of assignments.
    pub fn stack_len(&self) -> usize {
        self.trail.len()
    }
    /// return the number of assignments at a given decision level `u`.
    ///
    /// ## Caveat
    /// - it emits a panic by out of index range.
    /// - it emits a panic if the level is 0.
    pub fn len_upto(&self, n: DecisionLevel) -> usize {
        self.trail_lim.get(n as usize).map_or(0, |n| *n)
    }
    /// return `true` if there's no assignment.
    pub fn stack_is_empty(&self) -> bool {
        self.trail.is_empty()
    }
    /// return an iterator over assignment stack.
    pub fn stack_iter(&self) -> Iter<'_, Lit> {
        self.trail.iter()
    }
    /// return the current decision level.
    pub fn decision_level(&self) -> DecisionLevel {
        self.trail_lim.len() as DecisionLevel
    }
    ///return the decision var's id at that level.
    pub fn decision_vi(&self, lv: DecisionLevel) -> VarId {
        debug_assert!(0 < lv);
        self.trail[self.trail_lim[lv as usize - 1]].vi()
    }
    /// return `true` if there are un-propagated assignments.
    pub fn remains(&self) -> bool {
        self.q_head < self.trail.len()
    }
    /// return a reference to `assign`.
    pub fn assign_ref(&self) -> Vec<Option<bool>> {
        (0..=VarRef::num_vars())
            .map(|vi| VarRef(vi).assign())
            .collect::<Vec<_>>()
    }
    /// return the largest number of assigned vars.
    pub fn best_assigned(&self) -> Option<usize> {
        (self.build_best_at == self.num_propagations)
            .then_some(VarRef::num_vars() - self.num_best_assign)
    }
    /// return `true` if no best_phases
    #[cfg(feature = "rephase")]
    pub fn best_phases_invalid(&self) -> bool {
        self.best_phases.is_empty()
    }
    /// inject assignments for eliminated vars.
    #[allow(unused_variables)]
    pub fn extend_model(&self, cdb: &mut ClauseDB) -> Vec<Option<bool>> {
        let lits = &self.eliminated;

        #[cfg(feature = "trace_elimination")]
        println!(
            "# extend_model\n - as i32: {:?}\n - as raw: {:?}",
            i32s(lits),
            lits.iter()
                .map(|l| {
                    let i = i32::from(l);
                    if i < 0 {
                        -2 * i
                    } else {
                        2 * i + 1
                    }
                })
                .collect::<Vec<_>>(),
        );
        let mut extended_model: Vec<Option<bool>> = self.assign_ref();
        if lits.is_empty() {
            return extended_model;
        }
        let mut i = lits.len();
        while 0 < i {
            i -= 1;
            let width = usize::from(lits[i]);
            debug_assert!(0 < width);
            debug_assert!(width <= i);
            let target_index = i - width;
            let last_lit_index = i - 1;
            let reason_literals = target_index + 1..=last_lit_index;
            i = target_index;
            debug_assert!(
                lits[reason_literals.clone()]
                    .iter()
                    .all(|l| extended_model[l.vi()].is_some()),
                "impossible: pseudo clause has unassigned literal(s)."
            );
            if lits[reason_literals.clone()]
                .iter()
                .all(|l| extended_model[l.vi()] == Some(!bool::from(*l)))
            {
                let l = lits[target_index];
                extended_model[l.vi()] = Some(bool::from(l));
            } else if lits[reason_literals.clone()]
                .iter()
                .any(|l| extended_model[l.vi()] == Some(bool::from(*l)))
            {
                continue;
            }
        }
        extended_model
    }
}

impl fmt::Display for AssignStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let v = self.trail.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
        let levels = self.decision_level();
        let c = |i| match i {
            0 => {
                let a = self.len_upto(i);
                (0, &v[0..a])
            }
            x if x == levels => {
                let a = self.len_upto(levels - 1);
                (levels, &v[a..])
            }
            x => {
                let a = self.len_upto(x - 1);
                (x, &v[a..self.len_upto(x)])
            }
        };
        if 0 < levels {
            write!(
                f,
                "ASG:: trail({}):{:?}\n      stats: level: {}, asserted: {}, eliminated: {}",
                self.trail.len(),
                (0..=levels).map(c).collect::<Vec<_>>(),
                levels,
                self.num_asserted_vars,
                self.num_eliminated_vars,
            )
        } else {
            write!(
                f,
                "ASG:: trail({}):[(0, {:?})]\n      level: {}, asserted: {}, eliminated: {}",
                self.trail.len(),
                &v,
                levels,
                self.num_asserted_vars,
                self.num_eliminated_vars,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assign::PropagateIF;

    fn lit(i: i32) -> Lit {
        Lit::from(i)
    }
    #[test]
    fn test_propagation() {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        VarRef::instantiate(&config, &cnf);
        VarActivityManager::instantiate(&config, &cnf);
        let mut asg = AssignStack::instantiate(&config, &cnf);
        // [] + 1 => [1]
        assert!(asg.assign_at_root_level(lit(1)).is_ok());
        assert_eq!(asg.trail, vec![lit(1)]);

        // [1] + 1 => [1]
        assert!(asg.assign_at_root_level(lit(1)).is_ok());
        assert_eq!(asg.trail, vec![lit(1)]);

        // [1] + 2 => [1, 2]
        assert!(asg.assign_at_root_level(lit(2)).is_ok());
        assert_eq!(asg.trail, vec![lit(1), lit(2)]);

        // [1, 2] + -1 => ABORT & [1, 2]
        assert!(asg.assign_at_root_level(lit(-1)).is_err());
        assert_eq!(asg.decision_level(), 0);
        assert_eq!(asg.stack_len(), 2);

        // [1, 2] + 3 => [1, 2, 3]
        asg.assign_by_decision(lit(3));
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3)]);
        assert_eq!(asg.decision_level(), 1);
        assert_eq!(asg.stack_len(), 3);
        assert_eq!(asg.len_upto(0), 2);

        // [1, 2, 3] + 4 => [1, 2, 3, 4]
        asg.assign_by_decision(lit(4));
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3), lit(4)]);
        assert_eq!(asg.decision_level(), 2);
        assert_eq!(asg.stack_len(), 4);
        assert_eq!(asg.len_upto(1), 3);

        // [1, 2, 3] => [1, 2]
        #[cfg(feature = "debug_propagation")]
        {
            for l in asg.trail.iter() {
                asg.var[l.vi()].turn_on(Flag::PROPAGATED);
            } // simulate propagation
        }
        asg.cancel_until(1);
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3)]);
        assert_eq!(asg.decision_level(), 1);
        assert_eq!(asg.stack_len(), 3);
        assert_eq!(asg.trail_lim, vec![2]);
        assert_eq!(VarRef::lit_assigned(lit(1)), Some(true));
        assert_eq!(VarRef::lit_assigned(lit(-1)), Some(false));
        assert_eq!(VarRef::lit_assigned(lit(4)), None);

        // [1, 2, 3] => [1, 2, 3, 4]
        asg.assign_by_decision(lit(4));
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3), lit(4)]);
        // assert_eq!(asg.var[lit(4).vi()].level, 2);
        assert_eq!(VarRef(lit(4).vi()).level(), 2);
        assert_eq!(asg.trail_lim, vec![2, 3]);

        // [1, 2, 3, 4] => [1, 2, -4]
        asg.assign_at_root_level(Lit::from(-4i32))
            .expect("impossible");
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(-4)]);
        assert_eq!(asg.decision_level(), 0);
        assert_eq!(asg.stack_len(), 3);

        assert_eq!(VarRef::lit_assigned(lit(-4)), Some(true));
        assert_eq!(VarRef::lit_assigned(lit(-3)), None);
    }
}

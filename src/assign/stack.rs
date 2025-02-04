//! main struct AssignStack
use {
    super::{ema::ProgressASG, heap::VarHeapIF, heap::VarIdHeap, AssignIF, PropagateIF},
    crate::{cdb::ClauseDBIF, types::*, var_vector::*},
    std::{fmt, ops::Range, slice::Iter},
};

#[cfg(any(feature = "best_phases_tracking", feature = "rephase"))]
use std::collections::HashMap;

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
    pub root_level: DecisionLevel,
    pub(super) var_order: VarIdHeap, // Variable Order

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
    pub(super) best_phases: HashMap<VarId, (bool, AssignReason)>,
    #[cfg(feature = "rephase")]
    pub(super) phase_age: usize,

    //
    //## Stage
    //
    pub stage_scale: usize,

    //## Elimanated vars
    //
    pub eliminated: Vec<Lit>,

    //
    //## Statistics
    //
    /// the number of vars.
    pub num_vars: usize,
    /// the number of asserted vars.
    pub num_asserted_vars: usize,
    /// the number of eliminated vars.
    pub num_eliminated_vars: usize,
    pub(super) num_decision: usize,
    pub(super) num_propagation: usize,
    pub num_conflict: usize,
    pub(super) num_restart: usize,
    /// Assign rate EMA
    pub(super) assign_rate: ProgressASG,
    /// Decisions Per Conflict
    pub(super) dpc_ema: EmaSU,
    /// Propagations Per Conflict
    pub(super) ppc_ema: EmaSU,
    /// Conflicts Per Restart
    pub(super) cpr_ema: EmaSU,

    //
    //## Var DB
    //
    /// an index for counting elapsed time
    pub(super) tick: usize,
    // /// vars
    // pub(super) var: Vec<Var>,

    //
    //## Var Rewarding
    //
    /// var activity decay
    pub(super) activity_decay: f64,
    /// the default value of var activity decay in configuration
    #[cfg(feature = "EVSIDS")]
    activity_decay_default: f64,
    /// its diff
    pub(super) activity_anti_decay: f64,
    #[cfg(feature = "EVSIDS")]
    activity_decay_step: f64,
}

impl Default for AssignStack {
    fn default() -> AssignStack {
        AssignStack {
            trail: Vec::new(),
            trail_lim: Vec::new(),
            q_head: 0,
            root_level: 0,
            var_order: VarIdHeap::default(),

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
            best_phases: HashMap::new(),
            #[cfg(feature = "rephase")]
            phase_age: 0,

            stage_scale: 1,
            eliminated: Vec::new(),

            num_vars: 0,
            num_asserted_vars: 0,
            num_eliminated_vars: 0,
            num_decision: 0,
            num_propagation: 0,
            num_conflict: 0,
            num_restart: 0,
            assign_rate: ProgressASG::default(),
            dpc_ema: EmaSU::new(100),
            ppc_ema: EmaSU::new(100),
            cpr_ema: EmaSU::new(100),

            tick: 0,
            // var: Vec::new(),
            activity_decay: 0.94,

            #[cfg(feature = "EVSIDS")]
            activity_decay_default: 0.94,

            activity_anti_decay: 0.06,

            #[cfg(feature = "EVSIDS")]
            activity_decay_step: 0.1,
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
            var_order: VarIdHeap::new(nv),

            #[cfg(feature = "trail_saving")]
            trail_saved: Vec::with_capacity(nv),

            num_vars: cnf.num_of_variables,
            assign_rate: ProgressASG::instantiate(config, cnf),
            // var: Var::new_vars(nv),
            #[cfg(feature = "EVSIDS")]
            activity_decay: config.vrw_dcy_rat * 0.6,
            #[cfg(not(feature = "EVSIDS"))]
            activity_decay: config.vrw_dcy_rat,

            #[cfg(feature = "EVSIDS")]
            activity_decay_default: config.vrw_dcy_rat,

            activity_anti_decay: 1.0 - config.vrw_dcy_rat,
            #[cfg(feature = "EVSIDS")]
            activity_decay_step: config.vrw_dcy_stp,

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
                self.make_var_eliminated(vi);
            }
            SolverEvent::Stage(scale) => {
                self.stage_scale = scale;
                #[cfg(feature = "trail_saving")]
                self.clear_saved_trail();
            }
            SolverEvent::NewVar => {
                self.expand_heap();
                self.num_vars += 1;
                // self.var.push(Var::default());
                VarRef(0).add_var();
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

impl AssignIF for AssignStack {
    fn root_level(&self) -> DecisionLevel {
        self.root_level
    }
    fn stack(&self, i: usize) -> Lit {
        self.trail[i]
    }
    fn stack_range(&self, r: Range<usize>) -> &[Lit] {
        &self.trail[r]
    }
    fn stack_len(&self) -> usize {
        self.trail.len()
    }
    fn len_upto(&self, n: DecisionLevel) -> usize {
        self.trail_lim.get(n as usize).map_or(0, |n| *n)
    }
    fn stack_is_empty(&self) -> bool {
        self.trail.is_empty()
    }
    fn stack_iter(&self) -> Iter<'_, Lit> {
        self.trail.iter()
    }
    fn decision_level(&self) -> DecisionLevel {
        self.trail_lim.len() as DecisionLevel
    }
    fn decision_vi(&self, lv: DecisionLevel) -> VarId {
        debug_assert!(0 < lv);
        self.trail[self.trail_lim[lv as usize - 1]].vi()
    }
    fn remains(&self) -> bool {
        self.q_head < self.trail.len()
    }
    fn assign_ref(&self) -> Vec<Option<bool>> {
        (0..=self.num_vars)
            .map(|vi| VarRef(vi).assign())
            .collect::<Vec<_>>()
    }
    fn best_assigned(&mut self) -> Option<usize> {
        (self.build_best_at == self.num_propagation).then_some(self.num_vars - self.num_best_assign)
    }
    #[cfg(feature = "rephase")]
    fn best_phases_invalid(&self) -> bool {
        self.best_phases.is_empty()
    }
    #[allow(unused_variables)]
    fn extend_model(&mut self, cdb: &mut impl ClauseDBIF) -> Vec<Option<bool>> {
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
    fn satisfies(&self, vec: &[Lit]) -> bool {
        for l in vec {
            if self.assigned(*l) == Some(true) {
                return true;
            }
        }
        false
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
        assert_eq!(asg.assigned(lit(1)), Some(true));
        assert_eq!(asg.assigned(lit(-1)), Some(false));
        assert_eq!(asg.assigned(lit(4)), None);

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

        assert_eq!(asg.assigned(lit(-4)), Some(true));
        assert_eq!(asg.assigned(lit(-3)), None);
    }
}

/// Var manipulation
pub trait VarManipulateIF {
    /// return *the value* of a literal.
    fn assigned(&self, l: Lit) -> Option<bool>;
    // /// return the assignment of var.
    // fn assign(&self, vi: VarId) -> Option<bool>;
    // /// return the assign level of var.
    // fn level(&self, vi: VarId) -> DecisionLevel;
    // /// return the reason of assignment.
    // fn reason(&self, vi: VarId) -> AssignReason;
    // /// return the var.
    // fn var(&self, vi: VarId) -> &Var;
    // /// return the var.
    // fn var_mut(&mut self, vi: VarId) -> &mut Var;
    /// set var status to asserted.
    fn make_var_asserted(&mut self, vi: VarId);
    /// set var status to eliminated.
    fn make_var_eliminated(&mut self, vi: VarId);
}

impl VarManipulateIF for AssignStack {
    fn assigned(&self, l: Lit) -> Option<bool> {
        match VarRef(l.vi()).assign() /* self.var[l.vi()].assign */ {
            Some(x) if !bool::from(l) => Some(!x),
            x => x,
        }
    }
    // #[inline]
    // fn assign(&self, vi: VarId) -> Option<bool> {
    //     #[cfg(feature = "unsafe_access")]
    //     unsafe {
    //         self.var.get_unchecked(vi).assign
    //     }
    //     #[cfg(not(feature = "unsafe_access"))]
    //     self.assign[vi]
    // }
    // #[inline]
    // fn level(&self, vi: VarId) -> DecisionLevel {
    //     #[cfg(feature = "unsafe_access")]
    //     unsafe {
    //         self.var.get_unchecked(vi).level
    //     }
    //     #[cfg(not(feature = "unsafe_access"))]
    //     self.level[vi]
    // }
    // #[inline]
    // fn reason(&self, vi: VarId) -> AssignReason {
    //     #[cfg(feature = "unsafe_access")]
    //     unsafe {
    //         self.var.get_unchecked(vi).reason
    //     }
    //     #[cfg(not(feature = "unsafe_access"))]
    //     self.reason[vi]
    // }
    // #[inline]
    // fn var(&self, vi: VarId) -> &Var {
    //     #[cfg(feature = "unsafe_access")]
    //     unsafe {
    //         self.var.get_unchecked(vi)
    //     }
    //     #[cfg(not(feature = "unsafe_access"))]
    //     &self.var[vi]
    // }
    // #[inline]
    // fn var_mut(&mut self, vi: VarId) -> &mut Var {
    //     #[cfg(feature = "unsafe_access")]
    //     unsafe {
    //         self.var.get_unchecked_mut(vi)
    //     }
    //     #[cfg(not(feature = "unsafe_access"))]
    //     &mut self.var[vi]
    // }
    fn make_var_asserted(&mut self, vi: VarId) {
        // self.var[vi].reason = AssignReason::Decision(0);
        VarRef(vi).set_reason(AssignReason::Decision(0));
        self.set_activity(vi, 0.0);
        self.remove_from_heap(vi);

        #[cfg(feature = "boundary_check")]
        {
            self.var[vi].timestamp = self.tick;
        }

        #[cfg(feature = "best_phases_tracking")]
        self.check_best_phase(vi);
    }
    fn make_var_eliminated(&mut self, vi: VarId) {
        if !VarRef(vi).is(FlagVar::ELIMINATED) {
            VarRef(vi).turn_on(FlagVar::ELIMINATED);
            self.set_activity(vi, 0.0);
            self.remove_from_heap(vi);
            debug_assert_eq!(self.decision_level(), self.root_level);
            self.trail.retain(|l| l.vi() != vi);
            self.num_eliminated_vars += 1;

            #[cfg(feature = "boundary_check")]
            {
                self.var[vi].timestamp = self.tick;
            }

            #[cfg(feature = "trace_elimination")]
            {
                let lv = self.level[vi];
                if self.root_level == self.level[vi] && self.assign[vi].is_some() {
                    panic!("v:{}, dl:{}", self.var[vi], self.decision_level());
                }
                if !(self.root_level < self.level[vi] || self.assign[vi].is_none()) {
                    panic!(
                        "v:{}, lvl:{} => {}, dl:{}, assign:{:?} ",
                        self.var[vi],
                        lv,
                        self.level[vi],
                        self.decision_level(),
                        self.assign[vi],
                    );
                }
                debug_assert!(self.root_level < self.level[vi] || self.assign[vi].is_none());
            }
        } else {
            #[cfg(feature = "boundary_check")]
            panic!("double elimination");
        }
    }
}

#[cfg(feature = "best_phases_tracking")]
impl AssignStack {
    /// check usability of the saved best phase.
    /// return `true` if the current best phase got invalid.
    fn check_best_phase(&mut self, vi: VarId) -> bool {
        if let Some((b, _)) = self.best_phases.get(&vi) {
            debug_assert!(VarRef(vi).assign().is_some());
            if VarRef(vi).assign() != Some(*b) {
                if self.root_level == VarRef(vi).level() {
                    self.best_phases.clear();
                    self.num_best_assign = self.num_asserted_vars + self.num_eliminated_vars;
                }
                return true;
            }
        }
        false
    }
}

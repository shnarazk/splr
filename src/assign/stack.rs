/// main struct AssignStack
use {
    super::{ema::ProgressASG, AssignIF},
    crate::{cdb::ClauseDBIF, types::*},
    std::{fmt, ops::Range, slice::Iter},
};

#[cfg(any(feature = "best_phases_tracking", feature = "rephase"))]
use std::collections::HashMap;

#[cfg(feature = "trail_saving")]
use super::TrailSavingIF;

/// A record of assignment. It's called 'trail' in Glucose.
#[derive(Clone, Debug)]
pub struct AssignStack<'a> {
    /// record of assignment
    pub(crate) trail: Vec<Lit<'a>>,
    pub(crate) trail_lim: Vec<usize>,
    /// the-number-of-assigned-and-propagated-vars + 1
    pub(crate) q_head: usize,
    pub root_level: DecisionLevel,

    #[cfg(feature = "trail_saving")]
    pub(crate) trail_saved: Vec<Lit<'a>>,

    pub(crate) num_reconflict: usize,
    pub(crate) num_repropagation: usize,

    //
    //## Phase handling
    //
    pub(crate) best_assign: bool,
    pub(crate) build_best_at: usize,
    pub(crate) num_best_assign: usize,
    pub(crate) num_rephase: usize,
    pub(crate) bp_divergence_ema: Ema,

    #[cfg(feature = "best_phases_tracking")]
    pub(crate) best_phases: HashMap<VarId, (bool, AssignReason<'a>)>,
    #[cfg(feature = "rephase")]
    pub(crate) phase_age: usize,

    //
    //## Stage
    //
    pub stage_scale: usize,

    //## Elimanated vars
    //
    pub eliminated: Vec<Lit<'a>>,

    //
    //## Statistics
    //
    /// the number of vars.
    pub num_vars: usize,
    /// the number of asserted vars.
    pub num_asserted_vars: usize,
    /// the number of eliminated vars.
    pub num_eliminated_vars: usize,
    pub(crate) num_decision: usize,
    pub(crate) num_propagation: usize,
    pub num_conflict: usize,
    pub(crate) num_restart: usize,
    /// Assign rate EMA
    pub(crate) assign_rate: ProgressASG,
    /// Decisions Per Conflict
    pub(crate) dpc_ema: EmaSU,
    /// Propagations Per Conflict
    pub(crate) ppc_ema: EmaSU,
    /// Conflicts Per Restart
    pub(crate) cpr_ema: EmaSU,
}

impl<'a> Default for AssignStack<'a> {
    fn default() -> AssignStack<'static> {
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

            #[cfg(feature = "EVSIDS")]
            activity_decay_default: 0.94,
            #[cfg(feature = "EVSIDS")]
            activity_decay_step: 0.1,
        }
    }
}

impl<'a> IntoIterator for &'a mut AssignStack<'a> {
    type Item = &'a Lit<'a>;
    type IntoIter = Iter<'a, Lit<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        self.trail.iter()
    }
}

impl<'a> From<&mut AssignStack<'a>> for Vec<i32> {
    fn from(asg: &mut AssignStack<'a>) -> Vec<i32> {
        asg.trail.iter().map(|l| i32::from(*l)).collect::<Vec<_>>()
    }
}

impl Instantiate for AssignStack<'_> {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> AssignStack<'static> {
        let nv = cnf.num_of_variables;
        AssignStack {
            trail: Vec::with_capacity(nv),

            #[cfg(feature = "trail_saving")]
            trail_saved: Vec::with_capacity(nv),

            num_vars: cnf.num_of_variables,
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
            SolverEvent::Stage(scale) => {
                self.stage_scale = scale;
                #[cfg(feature = "trail_saving")]
                self.clear_saved_trail();
            }
            SolverEvent::NewVar => {
                self.num_vars += 1;
            }
            e => panic!("don't call asg with {e:?}"),
        }
    }
}

impl<'a> AssignIF<'a> for AssignStack<'a> {
    fn root_level(&self) -> DecisionLevel {
        self.root_level
    }
    fn stack(&'a self, i: usize) -> Lit<'a> {
        self.trail[i]
    }
    fn stack_range(&'a self, r: Range<usize>) -> &'a [Lit<'a>] {
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
    fn stack_iter(&'a self) -> Iter<'a, Lit<'a>> {
        self.trail.iter()
    }
    fn decision_level(&self) -> DecisionLevel {
        self.trail_lim.len() as DecisionLevel
    }
    fn decision_vi(&self, lv: DecisionLevel) -> VarId {
        debug_assert!(0 < lv);
        self.trail[self.trail_lim[lv as usize - 1]].var.id
    }
    fn remains(&self) -> bool {
        self.q_head < self.trail.len()
    }
    fn level_up(&mut self) {
        self.trail_lim.push(self.trail.len());
    }
    // fn assign_ref(&self) -> Vec<Option<bool>> {
    //     self.var.iter().map(|v| v.assign).collect::<Vec<_>>()
    // }
    fn best_assigned(&self) -> Option<usize> {
        (self.build_best_at == self.num_propagation).then_some(self.num_vars - self.num_best_assign)
    }
    #[cfg(feature = "rephase")]
    fn best_phases_invalid(&self) -> bool {
        self.best_phases.is_empty()
    }
    fn satisfies(&'a self, vec: &'a [Lit<'a>]) -> bool {
        for l in vec {
            if l.assigned() == Some(true) {
                return true;
            }
        }
        false
    }
}

impl fmt::Display for AssignStack<'_> {
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

// #[cfg(test)]
// mod tests {
//     use super::*;

//     fn lit(i: i32) -> Lit {
//         Lit::from(i)
//     }
//     #[test]
//     fn test_propagation() {
//         let config = Config::default();
//         let cnf = CNFDescription {
//             num_of_variables: 4,
//             ..CNFDescription::default()
//         };
//         let mut asg = AssignStack::instantiate(&config, &cnf);
//         // [] + 1 => [1]
//         assert!(asg.assign_at_root_level(lit(1)).is_ok());
//         assert_eq!(asg.trail, vec![lit(1)]);

//         // [1] + 1 => [1]
//         assert!(asg.assign_at_root_level(lit(1)).is_ok());
//         assert_eq!(asg.trail, vec![lit(1)]);

//         // [1] + 2 => [1, 2]
//         assert!(asg.assign_at_root_level(lit(2)).is_ok());
//         assert_eq!(asg.trail, vec![lit(1), lit(2)]);

//         // [1, 2] + -1 => ABORT & [1, 2]
//         assert!(asg.assign_at_root_level(lit(-1)).is_err());
//         assert_eq!(asg.decision_level(), 0);
//         assert_eq!(asg.stack_len(), 2);

//         // [1, 2] + 3 => [1, 2, 3]
//         asg.assign_by_decision(lit(3));
//         assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3)]);
//         assert_eq!(asg.decision_level(), 1);
//         assert_eq!(asg.stack_len(), 3);
//         assert_eq!(asg.len_upto(0), 2);

//         // [1, 2, 3] + 4 => [1, 2, 3, 4]
//         asg.assign_by_decision(lit(4));
//         assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3), lit(4)]);
//         assert_eq!(asg.decision_level(), 2);
//         assert_eq!(asg.stack_len(), 4);
//         assert_eq!(asg.len_upto(1), 3);

//         // [1, 2, 3] => [1, 2]
//         #[cfg(feature = "debug_propagation")]
//         {
//             for l in asg.trail.iter() {
//                 asg.var[l.vi()].turn_on(Flag::PROPAGATED);
//             } // simulate propagation
//         }
//         asg.cancel_until(1);
//         assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3)]);
//         assert_eq!(asg.decision_level(), 1);
//         assert_eq!(asg.stack_len(), 3);
//         assert_eq!(asg.trail_lim, vec![2]);
//         assert_eq!(asg.assigned(lit(1)), Some(true));
//         assert_eq!(asg.assigned(lit(-1)), Some(false));
//         assert_eq!(asg.assigned(lit(4)), None);

//         // [1, 2, 3] => [1, 2, 3, 4]
//         asg.assign_by_decision(lit(4));
//         assert_eq!(asg.trail, vec![lit(1), lit(2), lit(3), lit(4)]);
//         assert_eq!(asg.var[lit(4).vi()].level, 2);
//         assert_eq!(asg.trail_lim, vec![2, 3]);

//         // [1, 2, 3, 4] => [1, 2, -4]
//         asg.assign_at_root_level(Lit::from(-4i32))
//             .expect("impossible");
//         assert_eq!(asg.trail, vec![lit(1), lit(2), lit(-4)]);
//         assert_eq!(asg.decision_level(), 0);
//         assert_eq!(asg.stack_len(), 3);

//         assert_eq!(asg.assigned(lit(-4)), Some(true));
//         assert_eq!(asg.assigned(lit(-3)), None);
//     }
// }

#[cfg(feature = "best_phases_tracking")]
impl AssignStack {
    /// check usability of the saved best phase.
    /// return `true` if the current best phase got invalid.
    fn check_best_phase(&mut self, vi: VarId) -> bool {
        if let Some((b, _)) = self.best_phases.get(&vi) {
            debug_assert!(self.var[vi].assign.is_some());
            if self.var[vi].assign != Some(*b) {
                if self.root_level == self.var[vi].level {
                    self.best_phases.clear();
                    self.num_best_assign = self.num_asserted_vars + self.num_eliminated_vars;
                }
                return true;
            }
        }
        false
    }
}

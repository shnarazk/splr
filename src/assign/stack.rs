/// Crate `propagator` implements Boolean Constraint Propagation and decision var selection.
/// This version can handle Chronological and Non Chronological Backtrack.
use {
    super::{
        AssignIF, AssignStack, RewardStep, Var, VarIdHeap, VarManipulationIF, VarOrderIF, REWARDS,
    },
    crate::{clause::ClauseDBIF, state::State, types::*},
    std::{
        fmt,
        fs::File,
        io::{BufWriter, Write},
        ops::Range,
        slice::Iter,
    },
};

#[cfg(feature = "use_core")]
use crate::state::SearchStrategy;

macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
    };
}

/// API for var manipulation
pub trait ClauseManipulationIF {
    /// return `true` if the set of literals is satisfiable under the current assignment.
    fn satisfies(&self, c: &[Lit]) -> bool;
    /// return Option<bool>
    /// - Some(true) -- the literals is satisfied by a literal
    /// - Some(false) -- the literals is unsatisfied; no unassigned literal
    /// - None -- the literals contains an unassigned literal
    fn status(&self, c: &[Lit]) -> Option<bool>;
    /// return `true` is the clause is the reason of the assignment.
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool;
}

impl Default for AssignReason {
    fn default() -> AssignReason {
        AssignReason::None
    }
}

impl fmt::Display for AssignReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AssignReason::None => write!(f, "reason:none"),
            AssignReason::Implication(c, NULL_LIT) => write!(f, "reason:{}", c),
            AssignReason::Implication(c, _) => write!(f, "reason:biclause{}", c),
        }
    }
}

const CORE_HISOTRY_LEN: usize = 4000;

impl Default for AssignStack {
    fn default() -> AssignStack {
        // const VRD_START: f64 = 0.9;
        let reward = REWARDS[0];

        #[cfg(feature = "EVSIDS")]
        let reward_step = 1.0;

        #[cfg(not(feature = "EVSIDS"))]
        let reward_step = (reward.2 - reward.1) / 10_000.0;

        AssignStack {
            assign: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            q_head: 0,
            root_level: 0,
            conflicts: (0, 0),
            var_order: VarIdHeap::default(),
            num_vars: 0,
            num_solved_vars: 0,
            num_eliminated_vars: 0,
            best_assign: false,
            build_best_at: 0,
            num_best_assign: 0,
            target_assign: false,
            build_target_at: 0,
            num_target_assign: 0,
            num_conflict: 0,
            num_propagation: 0,
            num_restart: 0,
            ordinal: 0,
            var: Vec::new(),
            activity_decay: reward.1,
            activity_decay_max: reward.2,
            core_size: Ema::new(CORE_HISOTRY_LEN),
            reward_mode: RewardStep::HeatUp,
            reward_step,
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
    fn instantiate(_cfg: &Config, cnf: &CNFDescription) -> AssignStack {
        let nv = cnf.num_of_variables;
        AssignStack {
            assign: vec![None; 1 + nv],
            level: vec![DecisionLevel::default(); nv + 1],
            reason: vec![AssignReason::default(); 1 + nv],
            trail: Vec::with_capacity(nv),
            var_order: VarIdHeap::new(nv, nv),
            num_vars: cnf.num_of_variables,
            var: Var::new_vars(nv),
            ..AssignStack::default()
        }
    }
    #[allow(unused_variables)]
    fn adapt_to(&mut self, state: &State, num_conflict: usize) {
        #[cfg(feature = "use_core")]
        {
            const VRD_DEC_STRICT: f64 = 0.002;
            const VRD_DEC_STD: f64 = 0.002;
            const VRD_DEC_HIGH: f64 = 0.008;
            const VRD_INTERVAL: usize = 20_000;
            const VRD_FILTER: f64 = 0.5;
            const VRD_MAX_START: f64 = 0.2;
            const VRD_OFFSET: f64 = 10.0;

            if 0 == num_conflict {
                self.core_size
                    .update(((CORE_HISOTRY_LEN * self.var.len()) as f64).ln());
                return;
            }

            let msr: (f64, f64) = self.var[1..]
                .iter()
                .map(|v| v.reward)
                .fold((VRD_MAX_START, 0.0), |(m, s), x| (m.max(x), s + x));
            let ar = msr.1 / self.var.len() as f64;
            let thr = msr.0 * VRD_FILTER + ar * (1.0 - VRD_FILTER);
            let core = self.var[1..].iter().filter(|v| thr <= v.reward).count();
            // self.core_size.update(core as f64);

            if num_conflict % VRD_INTERVAL == 0 {
                let k = match state.strategy.0 {
                    SearchStrategy::LowDecisions => VRD_DEC_HIGH,
                    SearchStrategy::HighSuccesive => VRD_DEC_STRICT,
                    _ => VRD_DEC_STD,
                };
                let c = (self.core_size.get() - VRD_OFFSET).max(1.0);
                let delta = 0.1 * k * (c.sqrt() * c.ln());
                self.activity_decay_max = 1.0 - delta;

                const MB: f64 = 16.0;
                if self.reward_mode == RewardStep::Final {
                    self.activity_decay_max = VRD_MAX + k - 0.1 * self.core_size.get().min(MB) / MB;
                }
            }
        }

        #[cfg(not(feature = "use_core"))]
        {
            // if num_conflict % VRD_INTERVAL == 0 {
            //     let k = match state.strategy.0 {
            //         SearchStrategy::LowDecisions => VRD_DEC_HIGH,
            //         SearchStrategy::HighSuccesive => VRD_DEC_STRICT,
            //         _ => VRD_DEC_STD,
            //     };
            //     let delta = 10.0 * k;
            //     self.activity_decay_max = 1.0 - delta;
            // }
        }
    }
}

impl Export<(usize, usize, usize, f64, f64)> for AssignStack {
    /// exports:
    ///  1. the number of conflicts
    ///  1. the number of propagations
    ///  1. the number of restarts
    ///  1. `core_sise.get()`
    ///  1. `activity_decay`
    ///
    ///```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use crate::splr::assign::AssignStack;
    /// let asg = AssignStack::instantiate(&Config::default(), &CNFDescription::default());
    /// let (asg_num_conflict, asg_num_propagation, asg_num_restart, asg_core, asg_activity_decay) = asg.exports();
    ///```
    #[inline]
    fn exports(&self) -> (usize, usize, usize, f64, f64) {
        (
            self.num_conflict,
            self.num_propagation,
            self.num_restart,
            self.core_size.get(),
            self.activity_decay,
        )
    }
}

impl AssignIF for AssignStack {
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
        self.trail_lim[n as usize]
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
    fn recurrent_conflicts(&self) -> bool {
        self.conflicts.0 == self.conflicts.1
    }
    fn level_ref(&self) -> &[DecisionLevel] {
        &self.level
    }
    fn best_assigned(&mut self, flag: Flag) -> usize {
        match flag {
            Flag::BEST_PHASE => {
                if self.best_assign {
                    self.best_assign = false;
                    return self.num_best_assign;
                }
            }
            // Flag::TARGET_PHASE => {
            //     if self.target_assign {
            //         self.target_assign = false;
            //         return self.num_target_assign;
            //     }
            // }
            _ => panic!("invalid flag for reset_assign_record"),
        }
        0
    }
    fn extend_model(&mut self, lits: &[Lit]) {
        if lits.is_empty() {
            return;
        }
        let mut i = lits.len() - 1;
        let mut width;
        'next: loop {
            width = usize::from(lits[i]);
            if width == 0 && i == 0 {
                break;
            }
            i -= 1;
            loop {
                if width <= 1 {
                    break;
                }
                let l = lits[i];
                if self.assign(l.vi()) != Some(bool::from(l)) {
                    if i < width {
                        break 'next;
                    }
                    i -= width;
                    continue 'next;
                }
                width -= 1;
                i -= 1;
            }
            debug_assert!(width == 1);
            let l = lits[i];
            // debug_assert!(model[l.vi() - 1] != l.negate().int());
            self.assign[l.vi()] = Some(bool::from(l));
            if i < width {
                break;
            }
            i -= width;
        }
    }
}

impl AssignStack {
    /// dump all active clauses and fixed assignments as a CNF file.
    #[allow(dead_code)]
    fn dump_cnf<C, V>(&mut self, cdb: &C, fname: &str)
    where
        C: ClauseDBIF,
    {
        for vi in 1..self.var.len() {
            if self.var(vi).is(Flag::ELIMINATED) {
                if var_assign!(self, vi).is_some() {
                    panic!("conflicting var {} {:?}", vi, var_assign!(self, vi));
                } else {
                    println!("eliminate var {}", vi);
                }
            }
        }
        if let Ok(out) = File::create(&fname) {
            let mut buf = BufWriter::new(out);
            let nv = self.num_vars;
            let nc: usize = cdb.len() - 1;
            buf.write_all(format!("p cnf {} {}\n", self.num_vars, nc + nv).as_bytes())
                .unwrap();
            for c in cdb.iter().skip(1) {
                for l in &c.lits {
                    buf.write_all(format!("{} ", i32::from(*l)).as_bytes())
                        .unwrap();
                }
                buf.write_all(b"0\n").unwrap();
            }
            buf.write_all(b"c from trail\n").unwrap();
            for x in &self.trail {
                buf.write_all(format!("{} 0\n", i32::from(*x)).as_bytes())
                    .unwrap();
            }
        }
    }
}

impl fmt::Display for AssignStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let v = self.trail.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
        let len = self.decision_level();
        let c = |i| {
            let a = self.len_upto(i);
            match i {
                0 => (0, &v[0..a]),
                x if x == len - 1 => (i + 1, &v[a..]),
                x => (x + 1, &v[a..self.len_upto(x + 1)]),
            }
        };
        if 0 < len {
            write!(f, "{:?}", (0..len).map(c).collect::<Vec<_>>())
        } else {
            write!(f, "# - trail[  0]  [0{:?}]", &v)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert!(asg.assign_at_rootlevel(lit(1)).is_ok());
        assert_eq!(asg.trail, vec![lit(1)]);

        // [1] + 1 => [1]
        assert!(asg.assign_at_rootlevel(lit(1)).is_ok());
        assert_eq!(asg.trail, vec![lit(1)]);

        // [1] + 2 => [1, 2]
        assert!(asg.assign_at_rootlevel(lit(2)).is_ok());
        assert_eq!(asg.trail, vec![lit(1), lit(2)]);

        // [1, 2] + -1 => ABORT & [1, 2]
        assert!(asg.assign_at_rootlevel(lit(-1)).is_err());
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
        assert_eq!(asg.level[lit(4).vi()], 2);
        assert_eq!(asg.trail_lim, vec![2, 3]);

        // [1, 2, 3, 4] => [1, 2, -4]
        asg.assign_by_unitclause(Lit::from(-4i32));
        assert_eq!(asg.trail, vec![lit(1), lit(2), lit(-4)]);
        assert_eq!(asg.decision_level(), 0);
        assert_eq!(asg.stack_len(), 3);

        assert_eq!(asg.assigned(lit(-4)), Some(true));
        assert_eq!(asg.assigned(lit(-3)), None);
    }
}

/// Decision var selection
use {
    super::{AssignIF, AssignStack, Var, VarHeapIF, VarOrderIF, VarRewardIF},
    crate::{state::StagingTarget, types::*},
};

/// ```
/// let x: Option<bool> = var_assign!(self, lit.vi());
/// ```
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
    };
}

/// API for var selection, depending on an internal heap.
pub trait VarSelectIF {
    #[cfg(feature = "staging")]
    /// decay staging setting
    fn dissolve_stage(&mut self, phasing: bool);

    #[cfg(feature = "staging")]
    /// select staged vars
    fn take_stage(&mut self, target: StagingTarget);

    #[cfg(feature = "staging")]
    /// return the number of forgotton vars.
    fn num_staging_cands(&self) -> usize;

    /// select a new decision variable.
    fn select_decision_literal(&mut self) -> Lit;
    /// stage the vars is current assignments
    fn save_best_phases(&mut self);
    /// update the internal heap on var order.
    fn update_order(&mut self, v: VarId);
    /// rebuild the internal var_order
    fn rebuild_order(&mut self);
    /// make a var asserted.
    fn make_var_asserted(&mut self, vi: VarId);
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
struct VarTimestamp {
    timestamp: usize,
    vi: VarId,
}

impl From<&Var> for VarTimestamp {
    fn from(v: &Var) -> Self {
        VarTimestamp {
            timestamp: v.timestamp,
            vi: v.index,
        }
    }
}

impl VarSelectIF for AssignStack {
    #[cfg(feature = "staging")]
    fn dissolve_stage(&mut self, rephasing: bool) {
        self.rephasing = rephasing;
        for (vi, b) in self.staged_vars.iter() {
            let v = &mut self.var[*vi];
            v.set(Flag::PHASE, *b);
            v.extra_reward *= self.staging_reward_decay;
        }
    }
    #[cfg(feature = "staging")]
    fn num_staging_cands(&self) -> usize {
        let mut best_act_min: f64 = 100_000_000.0;
        for vi in self.best_phases.iter() {
            best_act_min = best_act_min.min(self.var[*vi.0].reward);
        }
        self.var
            .iter()
            .skip(1)
            .filter(|v| {
                !v.is(Flag::ELIMINATED)
                    && self.root_level < self.level[v.index]
                    && self.best_phases.get(&v.index).is_none()
                    && best_act_min <= v.reward
            })
            .count()
    }
    #[cfg(feature = "staging")]
    fn take_stage(&mut self, mut target: StagingTarget) {
        if target == StagingTarget::AutoSelect {
            let n = self.num_staging_cands();
            if 0 < n {
                target = StagingTarget::Extend((n as f64).sqrt() as usize)
            } else {
                // self.stage_mode_select += 1;
                match self.stage_mode_select % 3 {
                    // 1 => mode = StageMode::Extend((self.num_unreachable() as f64).sqrt() as usize),
                    // 2 => mode = StageMode::Best,
                    _ => {
                        for vi in self.best_phases.keys() {
                            let mut v = &mut self.var[*vi];
                            v.reward = 1.0 - (1.0 - v.reward).sqrt();
                        }
                        target = StagingTarget::Best;
                    }
                }
            }
        }
        for vi in self.staged_vars.keys() {
            self.var[*vi].extra_reward = 0.0;
        }
        self.staged_vars.clear();
        // self.staging_reward_value = self.staging_reward_value.sqrt();
        match target {
            StagingTarget::Best => {
                for (vi, b) in self.best_phases.iter() {
                    self.staged_vars.insert(*vi, *b);
                    self.var[*vi].extra_reward = self.staging_reward_value;
                    self.var[*vi].set(Flag::PHASE, *b);
                }
            }
            StagingTarget::Clear => (),
            StagingTarget::Extend(mut limit) => {
                for (vi, b) in self.best_phases.iter() {
                    self.staged_vars.insert(*vi, *b);
                    self.var[*vi].extra_reward = self.staging_reward_value;
                    self.var[*vi].set(Flag::PHASE, *b);
                }
                let len = self.var_order.idxs[0];
                for vi in self.var_order.heap[1..=len].iter() {
                    if self.root_level < self.level[*vi] && self.best_phases.get(&vi).is_none() {
                        assert!(!self.var[*vi].is(Flag::ELIMINATED));
                        if limit == 0 {
                            break;
                        }
                        limit -= 1;
                        let v = &mut self.var[*vi];
                        self.staged_vars.insert(*vi, v.is(Flag::PHASE));
                        v.extra_reward = self.staging_reward_value;
                    }
                }
            }
            StagingTarget::LastAssigned => {
                for vi in self.trail.iter().map(|l| l.vi()) {
                    let mut v = &mut self.var[vi];
                    self.staged_vars.insert(vi, v.is(Flag::PHASE));
                    v.extra_reward = self.staging_reward_value;
                }
            }
            StagingTarget::Random => {
                let limit = 10000;
                let _len = self.var_order.idxs[0].min(limit);
                for vi in self.var_order.heap[1..].iter().rev() {
                    let b = self.var[*vi].timestamp % 2 == 0;
                    self.staged_vars.insert(*vi, b);
                    self.var[*vi].extra_reward = self.staging_reward_value;
                }
            }
            #[cfg(feature = "explore_timestamp")]
            StagingTarget::Explore => {
                let since = self
                    .best_phases
                    .iter()
                    .map(|v| self.var[*v.0].assign_timestamp)
                    .min()
                    .unwrap_or(1);
                let len = self.var_order.idxs[0];
                for vi in self.var_order.heap[1..=len].iter() {
                    let v = &mut self.var[*vi];
                    if v.assign_timestamp < since {
                        self.staged_vars.insert(*vi, v.assign_timestamp % 2 == 0);
                        v.extra_reward = self.staging_reward_value;
                    }
                }
            }
            _ => (),
        }
    }
    fn select_decision_literal(&mut self) -> Lit {
        let vi = self.select_var();
        if self.use_rephase && self.rephasing {
            if let Some(b) = self.staged_vars.get(&vi) {
                return Lit::from_assign(vi, *b);
            }
        }
        Lit::from_assign(vi, self.var[vi].is(Flag::PHASE))
    }
    fn update_order(&mut self, v: VarId) {
        self.update_heap(v);
    }
    fn rebuild_order(&mut self) {
        self.var_order.clear();
        for vi in 1..self.var.len() {
            if var_assign!(self, vi).is_none() && !self.var[vi].is(Flag::ELIMINATED) {
                self.insert_heap(vi);
            }
        }
    }
    fn make_var_asserted(&mut self, vi: VarId) {
        self.num_asserted_vars += 1;
        self.clear_reward(vi);
        self.remove_from_heap(vi);
        self.check_best_phase(vi);
    }
}

impl AssignStack {
    /// check usability of the saved best phase.
    /// return `true` if the current best phase got invalid.
    fn check_best_phase(&mut self, vi: VarId) -> bool {
        if self.var[vi].is(Flag::ELIMINATED) {
            return false;
        }
        if self.level[vi] == self.root_level {
            return false;
        }
        if let Some(b) = self.staged_vars.get(&vi) {
            assert!(self.assign[vi].is_some());
            if self.assign[vi] != Some(*b) {
                self.best_phases.clear();
                self.num_best_assign = 0;
                return true;
            }
        }
        false
    }
    /// select a decision var
    fn select_var(&mut self) -> VarId {
        loop {
            let vi = self.get_heap_root();
            if var_assign!(self, vi).is_none() && !self.var[vi].is(Flag::ELIMINATED) {
                return vi;
            }
        }
    }
}

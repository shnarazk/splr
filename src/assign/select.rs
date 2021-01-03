#[cfg(feature = "temp_order")]
use std::collections::BinaryHeap;
/// Decision var selection
use {
    super::{AssignStack, Var, VarHeapIF, VarOrderIF, VarRewardIF},
    crate::{state::StageMode, types::*},
};

#[cfg(feature = "temp_order")]
use std::slice::Iter;

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
    #[cfg(feature = "temp_order")]
    /// force assignments
    fn force_select_iter(&mut self, iterator: Option<Iter<'_, usize>>);

    #[cfg(feature = "staging")]
    /// decay staging setting
    fn step_down_from_stage(&mut self, phasing: bool);

    #[cfg(feature = "staging")]
    /// force staging
    fn take_stage(&mut self, phase: StageMode);

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
    #[cfg(feature = "temp_order")]
    #[allow(unused_variables)]
    fn force_select_iter(&mut self, iterator: Option<Iter<'_, usize>>) {
        {
            if let Some(iter) = iterator {
                for vi in iter.rev() {
                    let lit = Lit::from_assign(*vi, self.var[*vi].is(Flag::PHASE));
                    self.temp_order.push(lit);
                }
            } else {
                let mut heap: BinaryHeap<VarTimestamp> = BinaryHeap::new();
                let remains = self.num_vars - self.num_asserted_vars - self.num_eliminated_vars;
                let size = (remains as f64).sqrt() as usize; //remains.count_ones() as usize;
                for v in self.var.iter().skip(1) {
                    if self.assign[v.index].is_some() {
                        continue;
                    }
                    if let Some(top) = heap.peek() {
                        if v.timestamp < top.timestamp {
                            heap.push(VarTimestamp::from(v));
                            if size < heap.len() {
                                heap.pop();
                            }
                        }
                    }
                }
                for v in heap.iter() {
                    let lit = Lit::from_assign(v.vi, self.var[v.vi].is(Flag::PHASE));
                    self.temp_order.push(lit);
                }
            }
        }
    }
    #[cfg(feature = "staging")]
    fn step_down_from_stage(&mut self, rephasing: bool) {
        self.rephasing = rephasing;
        for (vi, b) in self.staged_vars.iter() {
            let v = &mut self.var[*vi];
            v.set(Flag::PHASE, *b);

            #[cfg(feature = "extra_var_reward")]
            #[cfg(feature = "staging")]
            {
                v.extra_reward *= self.staging_reward_decay;
            }
        }
    }
    #[cfg(feature = "staging")]
    fn take_stage(&mut self, mut mode: StageMode) {
        if mode == StageMode::Scheduled {
            self.stage_index += 1;
            match self.stage_index % 3 {
                1 => mode = StageMode::Bottom3,
                //  => mode = StageMode::Middle3,
                2 => mode = StageMode::Top3,
                _ => mode = StageMode::Best,
            }
        }
        {
            for vi in self.staged_vars.keys() {
                self.var[*vi].extra_reward = 0.0;
            }
        }
        self.staged_vars.clear();
        #[cfg(feature = "temp_order")]
        {
            self.temp_order.clear();
        }
        // self.staging_reward_value = self.staging_reward_value.sqrt();
        match mode {
            StageMode::Bottom3 => {
                let len = self.var_order.idxs[0];
                // for vi in self.var_order.heap[(len * 2) / 3..len].iter() {
                for vi in self.var_order.heap[1..len / 2].iter() {
                    if true || !self.best_phases.get(vi).is_some() {
                        let mut v = &mut self.var[*vi];
                        self.staged_vars.insert(*vi, v.is(Flag::PHASE));
                        v.extra_reward = self.staging_reward_value;
                    }
                }
            }
            StageMode::Middle3 => {
                let len = self.var_order.idxs[0];
                for vi in self.var_order.heap[len / 3..len].iter() {
                    if self.best_phases.get(vi).is_some() {
                        let mut v = &mut self.var[*vi];
                        self.staged_vars.insert(*vi, v.is(Flag::PHASE));
                        v.extra_reward = self.staging_reward_value;
                    }
                }
            }
            StageMode::Top3 => {
                let len = self.var_order.idxs[0];
                for vi in self.var_order.heap[1..len / 2].iter() {
                    if true || self.best_phases.get(vi).is_some() {
                        let mut v = &mut self.var[*vi];
                        self.staged_vars.insert(*vi, v.is(Flag::PHASE));
                        v.extra_reward = self.staging_reward_value;
                    }
                }
            }
            StageMode::Best => {
                #[cfg(not(feature = "temp_order"))]
                {
                    for (vi, b) in self.best_phases.iter() {
                        {
                            self.staged_vars.insert(*vi, *b);
                            self.var[*vi].extra_reward = self.staging_reward_value;
                        }
                        self.var[*vi].set(Flag::PHASE, *b);
                    }
                }
                #[cfg(feature = "temp_order")]
                {
                    for (vi, b) in self.staged_vars.iter() {
                        self.temp_order.push(Lit::from_assign(vi, b));
                    }
                }
            }
            StageMode::Clear =>
            #[cfg(feature = "temp_order")]
            {
                for (vi, b) in self.staged_vars.iter() {
                    self.temp_order.push(Lit::from_assign(vi, b));
                }
            }
            StageMode::Explore => {
                let len = self.var_order.idxs[0];
                for vi in self.var_order.heap[len / 2..len].iter() {
                    let mut v = &mut self.var[*vi];
                    self.staged_vars.insert(*vi, v.is(Flag::PHASE));
                    v.extra_reward = self.staging_reward_value;
                }
            }
            StageMode::LastAssigned => {
                for vi in self.trail.iter().map(|l| l.vi()) {
                    let mut v = &mut self.var[vi];
                    self.staged_vars.insert(vi, v.is(Flag::PHASE));
                    v.extra_reward = self.staging_reward_value;
                }
            }
            #[cfg(feature = "explore_timestamp")]
            #[cfg(feature = "temp_order")]
            StageMode::Explore(since) => {
                for vi in self.var_order.heap[1..].iter() {
                    let v = &mut self.var[*vi];
                    if v.assign_timestamp < since {
                        self.temp_order
                            .push(Lit::from_assign(*vi, v.timestamp % 2 == 0));
                    }
                }
            }
            #[cfg(feature = "temp_order")]
            StageMode::Force(on) => {
                for vi in self.var_order.heap[1..].iter().rev() {
                    self.temp_order.push(Lit::from_assign(*vi, on));
                }
            }
            #[cfg(feature = "temp_order")]
            StageMode::Random => {
                let limit = 10000;
                let len = self.var_order.idxs[0].min(limit);
                for vi in self.var_order.heap[1..].iter().rev() {
                    let b = self.var[*vi].timestamp % 2 == 0;
                    self.temp_order.push(Lit::from_assign(*vi, b));
                }
            }
            StageMode::Scheduled => (),
        }
    }
    fn select_decision_literal(&mut self) -> Lit {
        #[cfg(feature = "temp_order")]
        {
            while let Some(lit) = self.temp_order.pop() {
                if self.assign[lit.vi()].is_none() && !self.var[lit.vi()].is(Flag::ELIMINATED) {
                    return lit;
                }
            }
        }
        let vi = self.select_var();
        if self.use_rephase && self.rephasing {
            if let Some(b) = self.staged_vars.get(&vi) {
                return Lit::from_assign(vi, *b);
            }
        }
        Lit::from_assign(vi, self.var[vi].is(Flag::PHASE))
    }
    fn save_best_phases(&mut self) {
        for l in self.trail.iter() {
            #[cfg(not(feature = "rephase_only_reason_vars"))]
            {
                let vi = l.vi();
                if let Some(b) = self.assign[vi] {
                    self.best_phases.insert(vi, b);
                }
            }
            #[cfg(feature = "rephase_only_reason_vars")]
            {
                if let AssignReason::Implication(_, lit) = self.reason[l.vi()] {
                    let vi = lit.vi();
                    if self.root_level < self.level[vi] {
                        if let Some(b) = self.assign[vi] {
                            self.rephasing_vars.insert(vi, b);
                        }
                    }
                }
            }
        }
        self.build_best_at = self.num_propagation;
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
    fn select_var(&mut self) -> VarId {
        loop {
            let vi = self.get_heap_root();
            if var_assign!(self, vi).is_none() && !self.var[vi].is(Flag::ELIMINATED) {
                return vi;
            }
        }
    }
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
                #[cfg(feature = "extra_var_reward")]
                #[cfg(feature = "staging")]
                {
                    for vj in self.staged_vars.keys() {
                        self.var[*vj].extra_reward = 0.0;
                    }
                }

                self.best_phases.clear();
                self.num_best_assign = 0;
                return true;
            }
        }
        false
    }
}

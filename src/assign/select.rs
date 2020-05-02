/// Decision var selection
use {
    super::{AssignStack, VarHeapIF, VarOrderIF, VarRewardIF},
    crate::{state::PhaseMode, types::*},
    std::slice::Iter,
};

/// ```
/// let x: Lbool = var_assign!(self, lit.vi());
/// ```
macro_rules! var_assign {
    ($asg: expr, $var: expr) => {
        unsafe { *$asg.assign.get_unchecked($var) }
    };
}

/// API for var selection, depending on an internal heap.
pub trait VarSelectIF {
    /// force assignments
    fn force_select_iter(&mut self, iterator: Iter<'_, usize>);
    /// force assignments
    fn force_select_from_phase(&mut self, phase: &PhaseMode);
    /// select a new decision variable.
    fn select_decision_literal(&mut self, phase: &PhaseMode) -> Lit;
    /// update the internal heap on var order.
    fn update_order(&mut self, v: VarId);
    /// rebuild the internal var_order
    fn rebuild_order(&mut self);
}

impl VarSelectIF for AssignStack {
    fn force_select_iter(&mut self, iterator: Iter<'_, usize>) {
        for vi in iterator.rev() {
            self.temp_order
                .push(Lit::from_assign(*vi, self.var[*vi].is(Flag::PHASE)));
        }
    }
    fn force_select_from_phase(&mut self, phase: &PhaseMode) {
        if self.temp_order.is_empty() && *phase == PhaseMode::Best {
            // PhaseMode::Worst => {
            //     for l in &self.unsat_trail {
            //         self.temp_order.push(*l);
            //     }
            // }
            for l in &self.best_trail {
                self.temp_order.push(*l);
            }
        }
    }
    fn select_decision_literal(&mut self, phase: &PhaseMode) -> Lit {
        if *phase != PhaseMode::Latest {
            while let Some(lit) = self.temp_order.pop() {
                if self.assign[lit.vi()].is_none() && !self.var[lit.vi()].is(Flag::ELIMINATED) {
                    return lit;
                }
            }
        }
        let vi = self.select_var();
        let p = match *phase {
            // PhaseMode::Best => asg.var(vi).is(Flag::BEST_PHASE),
            // PhaseMode::BestRnd => match ((asg.activity(vi) * 10000.0) as usize) % 8 {
            //     0 => asg.var(vi).is(Flag::BEST_PHASE),
            //     _ => asg.var(vi).is(Flag::PHASE),
            // },
            PhaseMode::Invert => !self.var[vi].is(Flag::PHASE),
            PhaseMode::Latest => self.var[vi].is(Flag::PHASE),
            PhaseMode::Random => ((self.activity(vi) * 10000.0) as usize) % 2 == 0,
            // PhaseMode::Target => self.var[vi].is(Flag::TARGET_PHASE),
            _ => self.var[vi].is(Flag::PHASE),
        };
        Lit::from_assign(vi, p)
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
}

use {
    super::AssignStack,
    crate::{types::*, var_vector::*},
    rustc_data_structures::fx::FxHashMap,
};

pub trait AssignRephaseIF {
    /// check usability of the saved best phase.
    /// return `true` if the current best phase got invalid.
    fn check_best_phase(&mut self, vi: VarId) -> bool;
    fn best_phases_ref(&mut self, default_value: Option<bool>) -> FxHashMap<VarId, bool>;
    fn override_rephasing_target(&mut self, assignment: &FxHashMap<VarId, bool>) -> usize;
    fn select_rephasing_target(&mut self);
    fn check_consistency_of_best_phases(&mut self);
}

impl AssignRephaseIF for AssignStack {
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
    fn best_phases_ref(&mut self, default_value: Option<bool>) -> FxHashMap<VarId, bool> {
        VarRef::var_id_iter()
            .filter_map(|vi| {
                if VarRef(vi).level() == self.root_level || VarRef(vi).is(FlagVar::ELIMINATED) {
                    default_value.map(|b| (vi, b))
                } else {
                    Some((
                        vi,
                        self.best_phases.get(&vi).map_or(
                            VarRef(vi)
                                .assign()
                                .unwrap_or_else(|| VarRef(vi).is(FlagVar::PHASE)),
                            |(b, _)| *b,
                        ),
                    ))
                }
            })
            .collect::<FxHashMap<VarId, bool>>()
    }
    fn override_rephasing_target(&mut self, assignment: &FxHashMap<VarId, bool>) -> usize {
        let mut num_flipped = 0;
        for (vi, b) in assignment.iter() {
            if self.best_phases.get(vi).is_none_or(|(p, _)| *p != *b) {
                num_flipped += 1;
                self.best_phases.insert(*vi, (*b, AssignReason::None));
            }
        }
        num_flipped
    }
    fn select_rephasing_target(&mut self) {
        if self.best_phases.is_empty() {
            return;
        }
        self.check_consistency_of_best_phases();
        if self.num_unasserted_vars() <= self.best_phases.len() {
            self.best_phases.clear();
            return;
        }
        debug_assert!(self
            .best_phases
            .iter()
            .all(|(vi, b)| VarRef(*vi).assign() != Some(!b.0)));
        self.num_rephase += 1;
        for (vi, (b, _)) in self.best_phases.iter() {
            VarRef(*vi).set_flag(FlagVar::PHASE, *b);
        }
    }
    fn check_consistency_of_best_phases(&mut self) {
        if self
            .best_phases
            .iter()
            .any(|(vi, b)| VarRef(*vi).assign() == Some(!b.0))
        {
            self.best_phases.clear();
            self.num_best_assign = self.num_asserted_vars + self.num_eliminated_vars;
        }
    }
}

//! Module `restart` provides restart heuristics.
use crate::types::*;

/// API for [`restart`](`crate::solver::RestartIF::restart`)
pub trait RestartIF: Instantiate {
    /// check blocking and forcing restart condition.
    fn restart(&mut self, ldb: &EmaView, ent: &EmaView) -> bool;
    /// set stabilization parameters
    fn set_stage_parameters(&mut self, step: usize);
    /// adjust restart threshold
    fn set_segment_parameters(&mut self, segment_scale: usize);
}

const FUEL: f64 = 0.01;

/// `RestartManager` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug, Default)]
pub struct RestartManager {
    // enable: bool,
    penetration_energy: f64,
    pub penetration_energy_charged: f64,
    penetration_energy_unit: f64,
}

impl Instantiate for RestartManager {
    fn instantiate(_config: &Config, _cnf: &CNFDescription) -> Self {
        RestartManager {
            // enable: true,
            penetration_energy: FUEL,
            penetration_energy_charged: FUEL,
            penetration_energy_unit: FUEL,
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        if e == SolverEvent::Restart {
            self.penetration_energy = self.penetration_energy_charged;
        }
    }
}

impl RestartIF for RestartManager {
    fn restart(&mut self, lbd: &EmaView, ent: &EmaView) -> bool {
        // if !self.enable { return false; }
        self.penetration_energy -= (lbd.trend() + ent.trend().min(1.0)) - 2.0;
        self.penetration_energy < 0.0
    }
    fn set_segment_parameters(&mut self, _segment_scale: usize) {
        self.penetration_energy_unit *= 10.0_f64.powf(-0.1);
    }
    fn set_stage_parameters(&mut self, stage_scale: usize) {
        // self.enable = !self.enable;
        let n = stage_scale.next_power_of_two() as f64;
        let e = self.penetration_energy_unit * n;
        self.penetration_energy_charged = e;
        self.penetration_energy = e;
    }
}

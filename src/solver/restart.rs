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

const FUEL: f64 = 1.0;
const SCALE: f64 = 0.25;

/// `RestartManager` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug, Default)]
pub struct RestartManager {
    penetration_energy: f64,
    pub penetration_energy_charged: f64,
    penetration_energy_unit: f64,
    field_scale: f64,
}

impl Instantiate for RestartManager {
    fn instantiate(_config: &Config, _cnf: &CNFDescription) -> Self {
        RestartManager {
            penetration_energy: FUEL,
            penetration_energy_charged: FUEL,
            penetration_energy_unit: FUEL,
            field_scale: 1.0 / SCALE,
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
        if cfg!(feature = "no_restart") {
            false
        } else {
            // let gscale = |x: f64| self.field_scale * (x - 1.0) + 1.0;
            // self.penetration_energy -= (lbd.trend() + gscale(ent.trend())) - 2.0;
            // self.penetration_energy < 0.0
            1.2 < lbd.trend()
        }
    }
    fn set_segment_parameters(&mut self, segment_scale: usize) {
        let factor = 0.5 * (segment_scale.trailing_zeros() + 1) as f64;
        self.field_scale = 1.0 / (SCALE - factor);
        self.penetration_energy_unit *= 10.0_f64.powf(-0.1);
    }
    fn set_stage_parameters(&mut self, stage_scale: usize) {
        let e = self.penetration_energy_unit * (stage_scale as f64);
        self.penetration_energy_charged = e;
        self.penetration_energy = e;
    }
}

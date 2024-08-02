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

/// `RestartManager` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug, Default)]
pub struct RestartManager {
    penetration_energy: f64,
    pub penetration_energy_charged: f64,
    penetration_energy_unit: f64,
}

impl Instantiate for RestartManager {
    fn instantiate(_config: &Config, _cnf: &CNFDescription) -> Self {
        RestartManager {
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
    fn restart(&mut self, lbd: &EmaView, _env: &EmaView) -> bool {
        if 0.1 < self.penetration_energy {
            // self.penetration_energy -= env.trend();
            self.penetration_energy -= 1.0 / 16.0;
            false
        } else {
            1.2 < lbd.trend()
        }
        /* self.penetration_energy = (self.penetration_energy - 0.3 * (lbd.trend() - 0.9))
            .min(self.penetration_energy_charged);
        self.penetration_energy < 0.0 */
    }
    fn set_segment_parameters(&mut self, _segment_scale: usize) {
        // self.penetration_energy_unit *= 10.0_f64.powf(-0.1);
    }
    fn set_stage_parameters(&mut self, stage_scale: usize) {
        // let e = self.penetration_energy_unit * (1.0 + stage_scale as f64).log2();
        let e = self.penetration_energy_unit * stage_scale as f64;
        self.penetration_energy_charged = e;
        self.penetration_energy = e;
    }
}

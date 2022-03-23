//! Crate `restart` provides restart heuristics.
use crate::types::*;

/// API for [`restart`](`crate::solver::RestartIF::restart`) and [`stabilize`](`crate::solver::RestartIF::stabilize`).
pub trait RestartIF: Instantiate + PropertyDereference<property::Tusize, usize> {
    /// check blocking and forcing restart condition.
    fn restart(&mut self, ema: &EmaView) -> bool;
    /// set stabilization parameters
    fn set_stage_parameters(&mut self, step: usize);
    /// adjust restart threshold
    fn set_segment_parameters(&mut self, segment_scale: usize);
}

const FUEL: f64 = 0.01;

/// `Restarter` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug, Default)]
pub struct Restarter {
    enable: bool,
    penetration_energy: f64,
    penetration_energy_charged: f64,
    penetration_energy_unit: f64,
    num_restart: usize,
}

impl Instantiate for Restarter {
    fn instantiate(_config: &Config, _cnf: &CNFDescription) -> Self {
        Restarter {
            enable: true,
            penetration_energy: FUEL,
            penetration_energy_charged: FUEL,
            penetration_energy_unit: FUEL,
            ..Restarter::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        if e == SolverEvent::Restart {
            self.penetration_energy = self.penetration_energy_charged;
            self.num_restart += 1;
        }
    }
}

impl RestartIF for Restarter {
    fn restart(&mut self, ema: &EmaView) -> bool {
        if self.enable {
            self.penetration_energy -= ema.trend() - 1.0;
            if self.penetration_energy < 0.0 {
                return true;
            }
        }
        false
    }
    /// minimize the difference between the number of restarts comparing
    /// and the expected number.
    fn set_segment_parameters(&mut self, _segment_scale: usize) {
        self.penetration_energy_unit *= 0.8;
    }
    fn set_stage_parameters(&mut self, stage_scale: usize) {
        // self.enable = !self.enable;
        self.penetration_energy_charged = self.penetration_energy_unit * (stage_scale as f64);
        // .powf(1.5);
    }
}

pub mod property {
    use super::Restarter;
    use crate::types::*;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Tbool {
        Active,
    }

    pub const BOOLS: [Tbool; 1] = [Tbool::Active];

    impl PropertyDereference<Tbool, bool> for Restarter {
        #[inline]
        fn derefer(&self, k: Tbool) -> bool {
            match k {
                Tbool::Active => self.enable,
            }
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Tusize {
        NumBlock,
        NumRestart,
    }

    pub const USIZES: [Tusize; 2] = [Tusize::NumBlock, Tusize::NumRestart];

    impl PropertyDereference<Tusize, usize> for Restarter {
        #[inline]
        fn derefer(&self, k: Tusize) -> usize {
            match k {
                Tusize::NumBlock => 0, // self.num_block,
                Tusize::NumRestart => self.num_restart,
            }
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Tf64 {
        RestartThreshold,
    }
    pub const F64S: [Tf64; 1] = [Tf64::RestartThreshold];

    impl PropertyDereference<Tf64, f64> for Restarter {
        #[inline]
        fn derefer(&self, k: Tf64) -> f64 {
            match k {
                Tf64::RestartThreshold => self.penetration_energy_charged,
            }
        }
    }
}

//! Crate `restart` provides restart heuristics.
use crate::types::*;

/// API for [`restart`](`crate::solver::RestartIF::restart`) and [`stabilize`](`crate::solver::RestartIF::stabilize`).
pub trait RestartIF: Instantiate + PropertyDereference<property::Tusize, usize> {
    /// check blocking and forcing restart condition.
    fn restart(&mut self, ent: &EmaView) -> Option<RestartDecision>;
    /// set stabilization parameters
    fn set_stage_parameters(&mut self, step: usize);
    /// adjust restart threshold
    fn set_segment_parameters(&mut self, span: usize, segment: usize);
}

const FUEL: f64 = 0.05;

/// `Restarter` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug, Default)]
pub struct Restarter {
    enable: bool,
    // /// For block restart based on average assignments: 1.40.
    // /// This is called `R` in Glucose.
    // block_threshold: f64,
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glucose.
    // restart_threshold: f64,
    penetration_energy: f64,
    penetration_energy_charged: f64,
    penetration_energy_default: f64,

    // stage parameter
    // stage_scale: usize,
    // max_scale: usize,

    //
    //## statistics
    //
    // num_block: usize,
    num_restart: usize,
    // num_restart_pre: usize,
}

impl Instantiate for Restarter {
    fn instantiate(_config: &Config, _cnf: &CNFDescription) -> Self {
        Restarter {
            enable: true,
            // block_threshold: config.rst_asg_thr,
            // restart_threshold: config.rst_lbd_thr,
            penetration_energy: FUEL,
            penetration_energy_charged: FUEL,
            penetration_energy_default: FUEL,
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

/// Type for the result of `restart`.
#[derive(Debug, Eq, PartialEq)]
pub enum RestartDecision {
    /// We should block restart.
    Block,
    /// We should restart now.
    Force,
}

impl RestartIF for Restarter {
    fn restart(&mut self, ent: &EmaView) -> Option<RestartDecision> {
        if self.enable {
            self.penetration_energy -= ent.trend() - 1.0;
            if self.penetration_energy < 0.0 {
                return Some(RestartDecision::Force);
            }
        }
        None
    }
    /// minimize the difference between the number of restarts comparing
    /// and the expected number.
    fn set_segment_parameters(&mut self, _span: usize, _segment: usize) {
        // self.penetration_energy_default = 0.01;
        // self.penetration_energy_default *= 0.75;
    }
    fn set_stage_parameters(&mut self, stage_scale: usize) {
        // self.enable = !self.enable;
        self.penetration_energy_charged =
            self.penetration_energy_default * (stage_scale as f64).powf(1.5);
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

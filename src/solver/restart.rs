//! Crate `restart` provides restart heuristics.
use crate::types::*;

/// API for [`restart`](`crate::solver::RestartIF::restart`) and [`stabilize`](`crate::solver::RestartIF::stabilize`).
pub trait RestartIF: Instantiate + PropertyDereference<property::Tusize, usize> {
    /// check blocking and forcing restart condition.
    fn restart(&mut self, asg: &EmaView, ent: &EmaView, lbd: &EmaView) -> Option<RestartDecision>;
    /// set stabilization parameters
    fn set_stage_parameters(&mut self, step: usize);
    /// adjust restart threshold
    fn set_segment_parameters(&mut self, max_scale: usize, segment: usize, max_scale: usize);
}

/// `Restarter` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug, Default)]
pub struct Restarter {
    // /// For block restart based on average assignments: 1.40.
    // /// This is called `R` in Glucose.
    // block_threshold: f64,
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glucose.
    restart_threshold: f64,

    penetration_energy: f64,
    penetration_energy_charged: f64,
    penetration_energy_default: f64,

    // stage parameter
    stage_scale: usize,
    max_scale: usize,

    //
    //## statistics
    //
    num_block: usize,
    num_restart: usize,
    num_restart_pre: usize,
}

impl Instantiate for Restarter {
    fn instantiate(config: &Config, _cnf: &CNFDescription) -> Self {
        Restarter {
            // block_threshold: config.rst_asg_thr,
            restart_threshold: config.rst_lbd_thr,
            penetration_energy: 2.5,
            penetration_energy_charged: 2.5,
            penetration_energy_default: 2.5,
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
    fn restart(
        &mut self,
        _asg: &EmaView,
        ent: &EmaView,
        _lbd: &EmaView,
    ) -> Option<RestartDecision> {
        // if self.max_scale * self.num_block < self.stage_scale * self.num_restart
        //     && asg.trend() < self.block_threshold
        // {
        //     self.num_block += 1;
        //     return Some(RestartDecision::Block);
        // }
        // let trend = lbd.trend() - 1.0;
        let trend = ent.trend() - 1.0;
        self.penetration_energy -= trend;
        if self.penetration_energy < 0.0 {
            return Some(RestartDecision::Force);
        }
        None
    }
    /// minimize the difference between the number of restarts comparing
    /// and the expected number.
    fn set_segment_parameters(&mut self, span: usize, segment: usize, max_scale: usize) {
        self.max_scale = max_scale;
        let ideal_interval: f64 = 10.0; // (self.initial_restart_step + 1) as f64;
        let dissipation: f64 = 0.1;
        // Since 'span' isn't a constant, a simple calculation may get a larger number.
        // To compensate the difference, I introduce another factor.
        let extends: f64 = span as f64 * 2.0_f64.powf(segment as f64 - dissipation);
        let expects = extends / ideal_interval;
        if expects < 100.0 {
            return;
        }
        // let scale = {
        //     let restarts = (self.num_restart - self.num_restart_pre) as f64;
        //     let center: f64 = 1.0;
        //     let s = restarts.log(expects) - center;
        //     center + s.signum() * s.abs().powf(1.4)
        // };
        // self.penetration_energy_default = self.penetration_energy_default.powf(scale);
        let restarts = (self.num_restart - self.num_restart_pre) as f64;
        self.penetration_energy_default *= (restarts / expects).powf(0.75);
        self.num_restart_pre = self.num_restart;
    }
    fn set_stage_parameters(&mut self, stage_scale: usize) {
        self.stage_scale = stage_scale;
        self.penetration_energy_charged =
            self.penetration_energy_default * (stage_scale as f64).powi(2);
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
                Tbool::Active => true,
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
                Tusize::NumBlock => self.num_block,
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
                Tf64::RestartThreshold => self.penetration_energy_default,
            }
        }
    }
}

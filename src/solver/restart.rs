//! Crate `restart` provides restart heuristics.
use crate::types::*;

/// API for [`restart`](`crate::solver::RestartIF::restart`) and [`stabilize`](`crate::solver::RestartIF::stabilize`).
pub trait RestartIF: Instantiate + PropertyDereference<property::Tusize, usize> {
    /// check blocking and forcing restart condition.
    fn restart(&mut self, asg: &EmaView, lbd: &EmaView) -> Option<RestartDecision>;
    /// set stabilization parameters
    fn setup_stage(&mut self, stage_scale: usize, c_lvl: f64, ent: f64);
    /// activate restart condition.
    fn setup_segment(&mut self, max_stage: usize);
}

/// `Restarter` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug, Default)]
pub struct Restarter {
    enable: bool,
    /// For block restart based on average assignments: 1.40.
    /// This is called `R` in Glucose.
    block_threshold: f64,
    restart_threshold: f64,

    // stabilizer
    stage_scale: usize,
    max_scale: usize,

    //
    //## statistics
    //
    num_block: usize,
    num_restart: usize,
}

impl Instantiate for Restarter {
    fn instantiate(config: &Config, _cnf: &CNFDescription) -> Self {
        Restarter {
            enable: true,
            block_threshold: config.rst_asg_thr,
            restart_threshold: 2.0,
            stage_scale: 1,
            max_scale: 1,
            ..Restarter::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        if e == SolverEvent::Restart {
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
    fn restart(&mut self, asg: &EmaView, lbd: &EmaView) -> Option<RestartDecision> {
        if !self.enable {
            return None;
        }
        if self.max_scale * self.num_block < self.stage_scale * self.num_restart
            && asg.trend() < self.block_threshold
        {
            self.num_block += 1;
            return Some(RestartDecision::Block);
        }
        let l = lbd.get_fast();
        if self.restart_threshold < l {
            return Some(RestartDecision::Force);
        }
        None
    }
    fn setup_segment(&mut self, max_scale: usize) {
        // self.enable = !self.enable;
        self.max_scale = max_scale;
    }
    fn setup_stage(&mut self, stage_scale: usize, _c_lvl: f64, ent: f64) {
        // self.enable = !self.enable;
        self.stage_scale = stage_scale;
        self.restart_threshold =
            // ent * (c_lvl / ent).powf(stage_scale as f64 / self.max_scale as f64);
        ent * ((stage_scale + 1) as f64).log(1.6)
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
                Tf64::RestartThreshold => self.restart_threshold,
            }
        }
    }
}

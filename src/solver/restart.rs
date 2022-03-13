//! Crate `restart` provides restart heuristics.
use {crate::types::*, splr_luby::LubySeries, std::fmt};

/// API for restart condition.
trait ProgressEvaluator {
    /// map the value into a bool for forcing/blocking restart.
    fn is_active(&self) -> bool;
    /// reset internal state to the initial one.
    fn reset_progress(&mut self) {}
    /// calculate and set up the next condition.
    fn shift(&mut self);
}

/// Update progress observer sub-modules
#[cfg(feature = "Luby_restart")]
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
enum ProgressUpdate {
    Counter,
    Luby,
}

/// API for [`restart`](`crate::solver::RestartIF::restart`) and [`stabilize`](`crate::solver::RestartIF::stabilize`).
pub trait RestartIF: Instantiate + PropertyDereference<property::Tusize, usize> {
    /// check blocking and forcing restart condition.
    fn restart(&mut self, asg: &EmaView, lbd: &EmaView) -> Option<RestartDecision>;
    /// set stabilization parameters
    fn set_sensibility(&mut self, step: usize, step_max: usize);
    #[cfg(feature = "dynamic_restart_threshold")]
    /// adjust restart threshold
    fn adjust_threshold(&mut self, max_scale: usize);
    #[cfg(feature = "Luby_restart")]
    /// update specific sub-module
    fn update(&mut self, kind: ProgressUpdate);

    #[cfg(feature = "Luby_restart")]
    /// dynamic adaptation of restart interval
    fn scale_restart_step(&mut self, scale: f64);
}

/// An EMA of decision level.
#[derive(Clone, Debug)]
struct ProgressLVL {
    ema: Ema2,
}

impl Instantiate for ProgressLVL {
    fn instantiate(_: &Config, _: &CNFDescription) -> Self {
        ProgressLVL {
            ema: Ema2::new(100).with_slow(800),
        }
    }
}

impl EmaIF for ProgressLVL {
    fn get_fast(&self) -> f64 {
        self.ema.get_fast()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl EmaMutIF for ProgressLVL {
    type Input = usize;
    fn update(&mut self, l: usize) {
        self.ema.update(l as f64);
    }
    fn as_view(&self) -> &EmaView {
        unimplemented!()
    }
}

impl ProgressEvaluator for ProgressLVL {
    fn is_active(&self) -> bool {
        todo!()
    }
    fn shift(&mut self) {}
}

/// An implementation of Luby series.
#[derive(Clone, Debug)]
struct ProgressLuby {
    enable: bool,
    active: bool,
    luby: LubySeries,
    next_restart: usize,
    step: usize,
}

impl Default for ProgressLuby {
    fn default() -> Self {
        const STEP: usize = 100;
        ProgressLuby {
            enable: false,
            active: false,
            luby: LubySeries::default(),
            next_restart: STEP,
            step: STEP,
        }
    }
}

impl Instantiate for ProgressLuby {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressLuby {
            enable: cfg!(feature = "Luby_restart"),
            step: config.rst_step,
            ..ProgressLuby::default()
        }
    }
}

impl fmt::Display for ProgressLuby {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.enable {
            write!(f, "Luby[step:{}]", self.next_restart)
        } else {
            write!(f, "Luby(deactivated)")
        }
    }
}

impl EmaIF for ProgressLuby {
    fn get_fast(&self) -> f64 {
        self.next_restart as f64
    }
}

impl EmaMutIF for ProgressLuby {
    type Input = usize;
    fn update(&mut self, now: usize) {
        if !self.enable {
            return;
        }
        self.active = self.next_restart < now;
    }
    fn as_view(&self) -> &EmaView {
        unimplemented!()
    }
}

impl ProgressEvaluator for ProgressLuby {
    fn is_active(&self) -> bool {
        self.enable && self.active
    }
    fn shift(&mut self) {
        self.active = false;
        self.next_restart = self.step * self.luby.next_unchecked();
    }
}

/// `Restarter` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug, Default)]
pub struct Restarter {
    /// For block restart based on average assignments: 1.40.
    /// This is called `R` in Glucose
    asg_threshold: f64,
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glucose
    lbd_threshold: f64,

    #[cfg(feature = "Luby_restart")]
    luby: ProgressLuby,

    after_restart: usize,
    restart_step: usize,
    initial_restart_step: usize,

    // stabilizer
    stb_step: usize,
    stb_step_max: usize,

    //
    //## statistics
    //
    num_block: usize,
    num_restart: usize,

    #[cfg(feature = "dynamic_restart_threshold")]
    num_restart_pre: usize,
}

impl Instantiate for Restarter {
    #[allow(unused_variables)]
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Self {
        Restarter {
            asg_threshold: config.rst_asg_thr,
            lbd_threshold: config.rst_lbd_thr,

            #[cfg(feature = "Luby_restart")]
            luby: ProgressLuby::instantiate(config, cnf),
            restart_step: config.rst_step,
            initial_restart_step: config.rst_step,

            ..Restarter::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        match e {
            SolverEvent::Assert(_) => (),
            SolverEvent::Restart => {
                self.after_restart = 0;
                self.num_restart += 1;
            }
            _ => (),
        }
    }
}

/// Type for the result of `restart`.
#[derive(Debug, PartialEq)]
pub enum RestartDecision {
    /// We should block restart.
    Block,
    /// We should restart now.
    Force,
}

impl RestartIF for Restarter {
    fn restart(&mut self, asg: &EmaView, lbd: &EmaView) -> Option<RestartDecision> {
        macro_rules! next_step {
            () => {
                self.stb_step * self.initial_restart_step
            };
        }
        self.after_restart += 1;
        #[cfg(feature = "Luby_restart")]
        {
            if self.luby.is_active() {
                self.luby.shift();
                self.restart_step = next_step!();
                return Some(RestartDecision::Force);
            }
        }
        if self.after_restart < self.restart_step {
            return None;
        }

        if self.stb_step_max * self.num_block < self.stb_step * self.num_restart
            && asg.trend() < self.asg_threshold
        {
            self.num_block += 1;
            self.after_restart = 0;
            self.restart_step = next_step!();
            return Some(RestartDecision::Block);
        }

        if self.lbd_threshold < lbd.trend() {
            self.restart_step = next_step!();
            return Some(RestartDecision::Force);
        }
        None
    }
    #[cfg(feature = "Luby_stabilization")]
    fn set_sensibility(&mut self, step: usize, step_max: usize) {
        self.stb_step = step;
        self.stb_step_max = step_max;
    }
    #[cfg(not(feature = "Luby_stabilization"))]
    fn set_stabilization(&mut self, _: usize, _: usize) -> Option<bool> {
        None
    }
    #[cfg(feature = "dynamic_restart_threshold")]
    fn adjust_threshold(&mut self, span: usize) {
        let center: f64 = 1.0;
        let increase = (self.num_restart - self.num_restart_pre) as f64;
        let scale = increase.log(span as f64) - center;
        if 0.25 < scale.abs() {
            self.lbd_threshold = self.lbd_threshold.powf(center + 0.5 * scale);
        }
        self.num_restart_pre = self.num_restart;
    }
    #[cfg(feature = "Luby_restart")]
    fn update(&mut self, kind: ProgressUpdate) {
        match kind {
            ProgressUpdate::Counter => {
                self.luby.update(self.after_restart);
            }
            // ProgressUpdate::ASG(val) => self.asg.update(val),
            ProgressUpdate::Luby => self.luby.update(0),
        }
    }
    #[cfg(feature = "Luby_restart")]
    fn scale_restart_step(&mut self, scale: f64) {
        const LIMIT: f64 = 1.2;
        let thr = self.lbd_threshold * scale;
        if LIMIT <= thr {
            self.lbd_threshold = thr;
        } else {
            self.lbd_threshold += LIMIT;
            self.lbd_threshold *= 0.5;
        }
    }
}

pub mod property {
    use super::Restarter;
    use crate::types::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
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

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Tf64 {
        RestartThreshold,
    }
    pub const F64S: [Tf64; 1] = [Tf64::RestartThreshold];

    impl PropertyDereference<Tf64, f64> for Restarter {
        #[inline]
        fn derefer(&self, k: Tf64) -> f64 {
            match k {
                Tf64::RestartThreshold => self.lbd_threshold,
            }
        }
    }
}

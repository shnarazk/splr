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
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub enum ProgressUpdate {
    ASG(usize),
    LBD(u16),
    Counter,

    #[cfg(feature = "Luby_restart")]
    Luby,
}

/// API for [`restart`](`crate::solver::RestartIF::restart`) and [`stabilize`](`crate::solver::RestartIF::stabilize`).
pub trait RestartIF:
    Instantiate
    + PropertyDereference<property::Tusize, usize>
    + PropertyReference<property::TEma2, EmaView>
{
    /// check blocking and forcing restart condition.
    fn restart(&mut self) -> Option<RestartDecision>;
    /// set stabilization parameters
    fn set_sensibility(&mut self, step: usize, step_max: usize);
    #[cfg(feature = "dynamic_restart_threshold")]
    /// adjust restart threshold
    fn adjust(&mut self, base: f64, c_lvl: f64, b_lvl: f64, used: f64);
    /// update specific sub-module
    fn update(&mut self, kind: ProgressUpdate);

    #[cfg(feature = "Luby_restart")]
    /// dynamic adaptation of restart interval
    fn scale_restart_step(&mut self, scale: f64);
}

const ASG_EWA_LEN: usize = 24;
const LBD_EWA_LEN: usize = 24;

/// An assignment history used for blocking restart.
#[derive(Clone, Debug)]
struct ProgressASG {
    enable: bool,
    ema: Ewa2<ASG_EWA_LEN>,
    /// For block restart based on average assignments: 1.40.
    /// This is called `R` in Glucose
    threshold: f64,
}

impl Default for ProgressASG {
    fn default() -> ProgressASG {
        ProgressASG {
            enable: true,
            ema: Ewa2::<ASG_EWA_LEN>::new(0.0),
            threshold: 1.4,
        }
    }
}

impl Instantiate for ProgressASG {
    fn instantiate(config: &Config, _cnf: &CNFDescription) -> Self {
        ProgressASG {
            ema: Ewa2::new(0.0).with_slow(config.rst_asg_slw),
            threshold: config.rst_asg_thr,
            ..ProgressASG::default()
        }
    }
}

impl EmaIF for ProgressASG {
    fn get_fast(&self) -> f64 {
        self.ema.get()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl EmaMutIF for ProgressASG {
    type Input = usize;
    fn update(&mut self, n: usize) {
        self.ema.update(n as f64);
    }
    fn as_view(&self) -> &EmaView {
        self.ema.as_view()
    }
}

impl ProgressEvaluator for ProgressASG {
    fn is_active(&self) -> bool {
        self.enable && self.trend() < self.threshold
    }
    fn shift(&mut self) {}
}

/// An EMA of learnt clauses' LBD, used for forcing restart.
#[derive(Clone, Debug)]
struct ProgressLBD {
    enable: bool,
    ema: Ewa2<LBD_EWA_LEN>,
    num: usize,
    sum: usize,
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glucose
    threshold: f64,
}

impl Default for ProgressLBD {
    fn default() -> ProgressLBD {
        ProgressLBD {
            enable: true,
            ema: Ewa2::<LBD_EWA_LEN>::new(0.0),
            num: 0,
            sum: 0,
            threshold: 1.4,
        }
    }
}

impl Instantiate for ProgressLBD {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressLBD {
            ema: Ewa2::new(0.0).with_slow(config.rst_lbd_slw),
            threshold: config.rst_lbd_thr,
            ..ProgressLBD::default()
        }
    }
}

impl EmaIF for ProgressLBD {
    fn get_fast(&self) -> f64 {
        self.ema.get_fast()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl EmaMutIF for ProgressLBD {
    type Input = u16;
    fn update(&mut self, d: Self::Input) {
        self.num += 1;
        self.sum += d as usize;
        self.ema.update(d as f64);
    }
    fn as_view(&self) -> &EmaView {
        self.ema.as_view()
    }
}

impl ProgressEvaluator for ProgressLBD {
    fn is_active(&self) -> bool {
        self.enable && self.threshold < self.trend()
    }
    fn shift(&mut self) {}
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
            #[cfg(feature = "Luby_restart")]
            enable: true,
            #[cfg(not(feature = "Luby_restart"))]
            enable: false,
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
    asg: ProgressASG,
    lbd: ProgressLBD,
    // pub blvl: ProgressLVL,
    // pub clvl: ProgressLVL,
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
}

impl Instantiate for Restarter {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Self {
        Restarter {
            asg: ProgressASG::instantiate(config, cnf),
            lbd: ProgressLBD::instantiate(config, cnf),
            // blvl: ProgressLVL::instantiate(config, cnf),
            // clvl: ProgressLVL::instantiate(config, cnf),
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
    fn restart(&mut self) -> Option<RestartDecision> {
        macro_rules! next_step {
            () => {
                self.stb_step * self.initial_restart_step
            };
        }
        if self.luby.is_active() {
            self.luby.shift();
            self.restart_step = next_step!();
            return Some(RestartDecision::Force);
        }

        if self.after_restart < self.restart_step {
            return None;
        }

        if self.stb_step_max * self.num_block < self.stb_step * self.num_restart
            && self.asg.is_active()
        {
            self.num_block += 1;
            self.after_restart = 0;
            self.restart_step = next_step!();
            return Some(RestartDecision::Block);
        }

        if self.lbd.is_active() {
            self.restart_step = next_step!();
            return Some(RestartDecision::Force);
        }
        None
    }
    #[cfg(feature = "Luby_stabilization")]
    fn set_sensibility(&mut self, step: usize, step_max: usize) {
        self.stb_step = step; // * step;
        self.stb_step_max = step_max; //  * step_max;
    }
    #[cfg(not(feature = "Luby_stabilization"))]
    fn set_stabilization(&mut self, _: usize, _: usize) -> Option<bool> {
        None
    }
    #[cfg(feature = "dynamic_restart_threshold")]
    fn adjust(&mut self, base: f64, c_lvl: f64, b_lvl: f64, used: f64) {
        const DECAY: f64 = 0.75;
        const CONTROL_FACTOR: f64 = 0.4;
        self.lbd.threshold *= DECAY;
        // * The larger ratio of conflicting level to backjumped level, the smaller threshold we need.
        //   Probably there are better clauses.
        // * The larger learnt clauses, compared with useful clauses, we get, the smaller threshold we need.
        //   Probably there are many bad branches.
        self.lbd.threshold += (1.0 - DECAY)
            * (c_lvl * self.lbd.ema.get() / b_lvl)
                .log(used)
                .max(1.0)
                .powf(CONTROL_FACTOR)
                .clamp(1.0, base);
    }
    fn update(&mut self, kind: ProgressUpdate) {
        match kind {
            ProgressUpdate::Counter => {
                self.after_restart += 1;
                self.luby.update(self.after_restart);
            }
            ProgressUpdate::ASG(val) => self.asg.update(val),
            ProgressUpdate::LBD(val) => {
                self.lbd.update(val);
            }

            #[cfg(feature = "Luby_restart")]
            ProgressUpdate::Luby => self.luby.update(0),
        }
    }
    #[cfg(feature = "Luby_restart")]
    fn scale_restart_step(&mut self, scale: f64) {
        const LIMIT: f64 = 1.2;
        let thr = self.lbd.threshold * scale;
        if LIMIT <= thr {
            self.lbd.threshold = thr;
        } else {
            self.lbd.threshold += LIMIT;
            self.lbd.threshold *= 0.5;
        }
        dbg!(self.lbd.threshold);
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
                Tf64::RestartThreshold => self.lbd.threshold,
            }
        }
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum TEma2 {
        ASG,
        LBD,
    }

    impl PropertyReference<TEma2, EmaView> for Restarter {
        #[inline]
        fn refer(&self, k: TEma2) -> &EmaView {
            match k {
                TEma2::ASG => &self.asg.as_view(),
                TEma2::LBD => &self.lbd.as_view(),
            }
        }
    }
}

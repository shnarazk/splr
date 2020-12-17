//! Crate `restart` provides restart heuristics.
use {
    crate::{
        solver::{SearchStrategy, SolverEvent},
        types::*,
    },
    std::fmt,
};

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
    Counter,

    #[cfg(progress_ACC)]
    ACC(f64),

    ASG(usize),
    LBD(u16),
    Luby,
    MLD(u16),
    Remain(usize),
}

/// Restart modes
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RestartMode {
    /// Controlled by Glucose-like forcing and blocking restart scheme
    Dynamic = 0,
    /// Controlled by a good old scheme
    Luby,
    /// Controlled by CaDiCal-like Geometric Stabilizer
    Stabilize,
    // Bucket,
}

/// API for restart like `block_restart`, `force_restart` and so on.
pub trait RestartIF {
    /// check blocking and forcing restart condition.
    fn restart(&mut self) -> Option<RestartDecision>;
    /// check stabilization mode.
    /// * just toggled
    /// * just into a new longest span
    fn stabilize(&mut self, now: usize) -> Option<(bool, bool)>;
    /// update specific sub-module
    fn update(&mut self, kind: ProgressUpdate);
}

/// An assignment history used for blocking restart.
#[derive(Debug)]
struct ProgressASG {
    enable: bool,
    ema: Ema2,
    /// For block restart based on average assignments: 1.40.
    /// This is called `R` in Glucose
    threshold: f64,
    nvar: usize,
}

impl Default for ProgressASG {
    fn default() -> ProgressASG {
        ProgressASG {
            enable: true,
            ema: Ema2::new(1),
            threshold: 1.4,
            nvar: 1,
        }
    }
}

impl Instantiate for ProgressASG {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Self {
        ProgressASG {
            ema: Ema2::new(config.rst_asg_len).with_slow(config.rst_asg_slw),
            threshold: config.rst_asg_thr,
            nvar: cnf.num_of_variables,
            ..ProgressASG::default()
        }
    }
}

impl EmaIF for ProgressASG {
    type Input = usize;
    fn update(&mut self, n: usize) {
        self.ema.update(n as f64);
    }
    fn get(&self) -> f64 {
        self.ema.get()
    }
    fn trend(&self) -> f64 {
        // self.ema.trend()
        let nv = self.nvar as f64;
        // (nv - self.ema.get_slow()) / (nv - self.ema.get())
        (self.ema.get() - self.ema.get_slow()) / nv
    }
}

impl ProgressEvaluator for ProgressASG {
    fn is_active(&self) -> bool {
        self.enable && self.threshold < self.trend()
    }
    fn shift(&mut self) {}
}

/// An EMA of learnt clauses' LBD, used for forcing restart.
#[derive(Debug)]
struct ProgressLBD {
    enable: bool,
    ema: Ema2,
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
            ema: Ema2::new(1),
            num: 0,
            sum: 0,
            threshold: 1.4,
        }
    }
}

impl Instantiate for ProgressLBD {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressLBD {
            ema: Ema2::new(config.rst_lbd_len).with_slow(config.rst_lbd_slw),
            threshold: config.rst_lbd_thr,
            ..ProgressLBD::default()
        }
    }
}

impl EmaIF for ProgressLBD {
    type Input = u16;
    fn update(&mut self, d: Self::Input) {
        self.num += 1;
        self.sum += d as usize;
        self.ema.update(d as f64);
    }
    fn get(&self) -> f64 {
        self.ema.get()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl ProgressEvaluator for ProgressLBD {
    fn is_active(&self) -> bool {
        self.enable && self.threshold < self.trend()
    }
    fn shift(&mut self) {}
}

/// An EMA of Maximum LBD of a Dependent graph, used in conflict analyze
#[derive(Debug)]
struct ProgressMLD {
    enable: bool,
    ema: Ema2,
    num: usize,
    sum: usize,
    scaling: f64,
    threshold: f64,
}

impl Default for ProgressMLD {
    fn default() -> ProgressMLD {
        ProgressMLD {
            enable: true,
            ema: Ema2::new(1),
            num: 0,
            sum: 0,
            scaling: 0.20,
            threshold: 2.0,
        }
    }
}

impl Instantiate for ProgressMLD {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressMLD {
            ema: Ema2::new(config.rst_lbd_len).with_slow(config.rst_lbd_slw),
            scaling: config.rst_mld_scl,
            threshold: config.rst_mld_thr,
            ..ProgressMLD::default()
        }
    }
}

impl EmaIF for ProgressMLD {
    type Input = u16;
    fn update(&mut self, d: Self::Input) {
        self.num += 1;
        self.sum += d as usize;
        self.ema.update(d as f64);
    }
    fn get(&self) -> f64 {
        self.ema.get()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl ProgressEvaluator for ProgressMLD {
    fn is_active(&self) -> bool {
        self.enable && self.threshold < self.ema.trend()
    }
    fn shift(&mut self) {}
}

#[cfg(progress_ACC)]
/// An EMA of Activity-based Conflict Correlation, used for forcing restart.
#[derive(Debug)]
struct ProgressACC {
    enable: bool,
    ema: Ema2,
    num: usize,
    sum: f64,
    // increment by update
    val: f64,
    // increment by update
    inc: usize,
    // storing the last check result
    correlation: f64,
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glucose
    threshold: f64,
}

#[cfg(progress_ACC)]
impl Default for ProgressACC {
    fn default() -> ProgressACC {
        ProgressACC {
            enable: true,
            ema: Ema2::new(1),
            num: 0,
            sum: 0.0,
            val: 0.0,
            inc: 0,
            correlation: 0.0,
            threshold: 1.6,
        }
    }
}

#[cfg(progress_ACC)]
impl Instantiate for ProgressACC {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressACC {
            ema: Ema2::new(config.rst_lbd_len).with_slow(config.rst_lbd_slw),
            threshold: config.rst_ccc_thr,
            ..ProgressACC::default()
        }
    }
}

#[cfg(progress_ACC)]
impl EmaIF for ProgressACC {
    type Input = f64;
    fn update(&mut self, d: Self::Input) {
        self.inc += 1;
        self.val += d;
    }
    fn get(&self) -> f64 {
        self.ema.get()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

#[cfg(progress_ACC)]
impl ProgressEvaluator for ProgressACC {
    // Smaller core, larger value
    fn is_active(&self) -> bool {
        self.enable && self.threshold < self.correlation
    }
    fn shift(&mut self) {
        if 0 < self.inc {
            self.num += 1;
            self.sum += self.val;
            self.correlation = self.val / (self.inc as f64);
            self.ema.update(self.correlation);
            self.val = 0.0;
            self.inc = 0;
        }
    }
}

/// An EMA of decision level.
#[derive(Debug)]
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
    type Input = usize;
    fn update(&mut self, l: usize) {
        self.ema.update(l as f64);
    }
    fn get(&self) -> f64 {
        self.ema.get()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl ProgressEvaluator for ProgressLVL {
    fn is_active(&self) -> bool {
        todo!()
    }
    fn shift(&mut self) {}
}

/// An EMA of recurring conflict complexity (unused now).
#[derive(Debug)]
struct ProgressRCC {
    heat: Ema2,
    threshold: f64,
}

impl Default for ProgressRCC {
    fn default() -> Self {
        ProgressRCC {
            heat: Ema2::new(100).with_slow(8000),
            threshold: 0.0,
        }
    }
}

impl Instantiate for ProgressRCC {
    fn instantiate(_: &Config, _: &CNFDescription) -> Self {
        ProgressRCC::default()
    }
}

impl fmt::Display for ProgressRCC {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "ProgressRCC[heat:{}, thr:{}]",
            self.get(),
            self.threshold
        )
    }
}

impl EmaIF for ProgressRCC {
    type Input = f64;
    fn update(&mut self, foc: Self::Input) {
        self.heat.update(foc);
    }
    fn get(&self) -> f64 {
        self.heat.get()
    }
    fn trend(&self) -> f64 {
        self.heat.trend()
    }
}

impl ProgressEvaluator for ProgressRCC {
    fn is_active(&self) -> bool {
        self.threshold < self.heat.get()
    }
    fn shift(&mut self) {}
}

/// An implementation of Luby series.
#[derive(Debug)]
struct ProgressLuby {
    enable: bool,
    active: bool,
    luby: LubySeries,
    next_restart: usize,
    restart_inc: f64,
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
            restart_inc: 2.0,
            step: STEP,
        }
    }
}

impl Instantiate for ProgressLuby {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressLuby {
            enable: config.use_luby(),
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
    type Input = usize;
    fn update(&mut self, now: usize) {
        if !self.enable {
            return;
        }
        /* if index == 0 {
            self.index = 0;
            self.next_restart = self.next_step();
            self.active = false;
        } else {
            self.active = self.next_restart < index;
        } */
        self.active = self.next_restart < now;
    }
    fn get(&self) -> f64 {
        self.next_restart as f64
    }
}

impl ProgressEvaluator for ProgressLuby {
    fn is_active(&self) -> bool {
        self.enable && self.active
    }
    fn shift(&mut self) {
        self.active = false;
        self.next_restart = self.step * self.luby.next().unwrap();
    }
}

/// Find the finite subsequence that contains index 'x', and the
/// size of that subsequence as: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8
impl ProgressLuby {
    /*
    fn next_step(&self) -> usize {
        if self.index == 0 {
            return self.step;
        }
        let mut size: usize = 1;
        let mut seq: usize = 0;
        while size < self.index + 1 {
            seq += 1;
            size = 2 * size + 1;
        }
        let mut x = self.index;
        while size - 1 != x {
            size = (size - 1) >> 1;
            seq -= 1;
            x %= size;
        }
        (self.restart_inc.powf(seq as f64) * self.step as f64) as usize
    }
    */
}

/// An implementation of CaDiCaL-style blocker.
/// This is a stealth blocker between the other evaluators and solver;
/// the other evaluators work as if this blocker doesn't exist.
/// When an evaluator becomes active, we accept and shift it. But this blocker
/// absorbs not only the forcing signal but also blocking signal.
/// This exists in macro `reset`.
#[derive(Debug)]
struct GeometricStabilizer {
    enable: bool,
    active: bool,
    longest_span: usize,
    luby: LubySeries,
    num_shift: usize,
    next_trigger: usize,
    reset_requested: bool,
    step: usize,
    scale: usize,
}

impl Default for GeometricStabilizer {
    fn default() -> Self {
        const STEP: usize = 64;
        GeometricStabilizer {
            enable: true,
            active: false,
            longest_span: 1,
            luby: LubySeries::default(),
            num_shift: 0,
            next_trigger: STEP,
            reset_requested: false,
            step: 1,
            scale: STEP,
        }
    }
}

impl Instantiate for GeometricStabilizer {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        GeometricStabilizer {
            enable: config.use_stabilize(),
            ..GeometricStabilizer::default()
        }
    }
}

impl fmt::Display for GeometricStabilizer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.enable {
            write!(f, "Stabilizer(dead)")
        } else if self.active && self.enable {
            write!(
                f,
                "Stabilizer[step: {}, next:{}, on]",
                self.step, self.next_trigger
            )
        } else {
            write!(
                f,
                "Stabilizer[step: {}, next:{}, off]",
                self.step, self.next_trigger
            )
        }
    }
}

impl GeometricStabilizer {
    fn update(&mut self, now: usize) -> Option<(bool, bool)> {
        if self.enable && self.next_trigger <= now {
            self.num_shift += 1;
            self.active = !self.active;
            let mut new_cycle: bool = false;
            if self.reset_requested {
                // reset doesn't start a new cycle; it's a kind of redo.
                self.luby.reset();
                self.reset_requested = false;
            } else if self.longest_span < self.step {
                new_cycle = true;
                self.longest_span = self.step;
                if self.reset_requested {
                    self.reset_requested = false;
                }
            }
            self.step = self.luby.next().unwrap();
            // assert!(!new_cycle || self.step == 1);
            self.next_trigger = now + self.step * self.scale;
            Some((self.active, new_cycle))
        } else {
            None
        }
    }
    fn span(&self) -> usize {
        self.step
    }
    fn reset_progress(&mut self) {
        self.reset_requested = true;
    }
    fn new(enable: bool, step: usize) -> Self {
        GeometricStabilizer {
            enable,
            active: false,
            longest_span: 1,
            luby: LubySeries::default(),
            num_shift: 0,
            next_trigger: step,
            reset_requested: false,
            step,
            scale: step,
        }
    }
}

/*
/// Restart when LBD's sum is over a limit.
#[derive(Debug)]
struct ProgressBucket {
    enable: bool,
    num_shift: usize,
    sum: f64,
    power: f64,
    power_factor: f64,
    power_scale: f64,
    step: f64,
    threshold: f64,
}

impl Default for ProgressBucket {
    fn default() -> ProgressBucket {
        ProgressBucket {
            enable: false,
            num_shift: 0,
            sum: 0.0,
            power: 1.25,
            power_factor: 1.25,
            power_scale: 0.0,
            step: 1.0,
            threshold: 2000.0,
        }
    }
}

impl Instantiate for ProgressBucket {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressBucket {
            power: config.rst_bkt_pwr,
            power_factor: (config.rst_bkt_pwr - 1.0).max(0.0),
            power_scale: config.rst_bkt_scl,
            step: config.rst_bkt_inc,
            threshold: config.rst_bkt_thr as f64,
            ..ProgressBucket::default()
        }
    }
}

impl EmaIF for ProgressBucket {
    type Input = usize;
    fn update(&mut self, d: usize) {
        self.sum += (d as f64).powf(self.power);
    }
    fn get(&self) -> f64 {
        todo!()
    }
    fn trend(&self) -> f64 {
        todo!()
    }
}

impl ProgressEvaluator for ProgressBucket {
    fn is_active(&self) -> bool {
        self.enable && self.threshold < self.sum
    }
    fn reset_progress(&mut self) {
        if self.enable {
            self.num_shift = 1;
            self.threshold = 1000.0; // FIXME: we need the values in config
            self.shift();
        }
    }
    fn shift(&mut self) {
        self.num_shift += 1;
        self.sum = 0.0;
        self.threshold += self.step;
        // self.power = 1.0 + (self.num_shift as f64).powf(-0.2);
        // self.power = 1.0 + (1.0 + 0.001 * self.num_shift as f64).powf(-1.0);
        if 0.0 < self.power_factor {
            // If power_scale == 0.0, then p == 1.0 and power == config.rst_bkt_pwr.
            let p = (1.0 + self.power_scale * self.num_shift as f64).powf(-1.0);
            self.power = 1.0 + self.power_factor * p;
        }
    }
}
 */

/// `Restarter` provides restart API and holds data about restart conditions.
#[derive(Debug)]
pub struct Restarter {
    #[cfg(progress_ACC)]
    acc: ProgressACC,

    asg: ProgressASG,
    // bkt: ProgressBucket,
    lbd: ProgressLBD,
    mld: ProgressMLD,
    // pub rcc: ProgressRCC,
    // pub blvl: ProgressLVL,
    // pub clvl: ProgressLVL,
    luby: ProgressLuby,
    luby_blocking: GeometricStabilizer,
    stb: GeometricStabilizer,
    after_restart: usize,
    restart_step: usize,
    initial_restart_step: usize,

    //
    //## statistics
    //
    num_block: usize,
    num_restart: usize,
}

impl Default for Restarter {
    fn default() -> Restarter {
        Restarter {
            #[cfg(progress_ACC)]
            acc: ProgressACC::default(),

            asg: ProgressASG::default(),
            // bkt: ProgressBucket::default(),
            lbd: ProgressLBD::default(),
            mld: ProgressMLD::default(),
            // rcc: ProgressRCC::default(),
            // blvl: ProgressLVL::default(),
            // clvl: ProgressLVL::default(),
            luby: ProgressLuby::default(),
            luby_blocking: GeometricStabilizer::new(true, 0),
            stb: GeometricStabilizer::default(),
            after_restart: 0,
            restart_step: 0,
            initial_restart_step: 0,
            num_block: 0,
            num_restart: 0,
        }
    }
}

impl Instantiate for Restarter {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Self {
        Restarter {
            #[cfg(progress_ACC)]
            acc: ProgressACC::instantiate(config, cnf),

            asg: ProgressASG::instantiate(config, cnf),
            // bkt: ProgressBucket::instantiate(config, cnf),
            lbd: ProgressLBD::instantiate(config, cnf),
            mld: ProgressMLD::instantiate(config, cnf),
            // rcc: ProgressRCC::instantiate(config, cnf),
            // blvl: ProgressLVL::instantiate(config, cnf),
            // clvl: ProgressLVL::instantiate(config, cnf),
            luby: ProgressLuby::instantiate(config, cnf),
            stb: GeometricStabilizer::instantiate(config, cnf),
            restart_step: config.rst_step,
            initial_restart_step: config.rst_step,
            ..Restarter::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        match e {
            SolverEvent::Adapt((SearchStrategy::Initial, 0), _) => {
                // self.int.enable = true;
            }
            SolverEvent::Adapt((SearchStrategy::LowSuccessive, n), m) if n == m => {
                // self.luby.enable = true;
            }
            SolverEvent::Assert(_) => {
                self.luby_blocking.reset_progress();
                self.stb.reset_progress();
            }
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
    /// TODO
    Postpone,
    /// We are in stabilization mode.
    Stabilize,
}

impl RestartIF for Restarter {
    #[inline]
    #[allow(clippy::collapsible_if)]
    fn restart(&mut self) -> Option<RestartDecision> {
        if self.luby.is_active() {
            self.luby.shift();
            return Some(RestartDecision::Force);
        }
        if self.after_restart < self.restart_step {
            return None;
        }
        // self.acc.shift();

        // Branching based on sizes of learnt clauses comparing with the average of
        // maximum LBDs used in conflict analysis.
        // let _good_path = self.lbd.get()
        //     < self.mld.get() + (self.stb.span() as f64) * self.mld.scaling + self.mld.threshold;

        if self.stb.active {
            return Some(RestartDecision::Stabilize);
        }

        if self.asg.is_active() {
            self.num_block += 1;
            self.after_restart = 0;
            // self.luby_blocking.update(0);
            self.restart_step = self.initial_restart_step * self.stb.span();
            // self.restart_step = self.initial_restart_step;
            return Some(RestartDecision::Block);
        }

        let threshold = self.lbd.threshold; // (1.0 + self.stb.span() as f64).log(2.0);
        if threshold < self.lbd.trend()
        /* .lbd.is_active() */
        {
            self.restart_step = self.initial_restart_step;
            return Some(RestartDecision::Force);
        }
        Some(RestartDecision::Postpone)
    }
    fn stabilize(&mut self, now: usize) -> Option<(bool, bool)> {
        self.stb.update(now)
    }
    fn update(&mut self, kind: ProgressUpdate) {
        match kind {
            ProgressUpdate::Counter => {
                self.after_restart += 1;
                self.luby.update(self.after_restart);
            }

            #[cfg(progress_ACC)]
            ProgressUpdate::ACC(_) => (), // self.acc.update(fval),

            ProgressUpdate::ASG(val) => self.asg.update(val),
            ProgressUpdate::LBD(val) => self.lbd.update(val),
            ProgressUpdate::Luby => self.luby.update(0),
            ProgressUpdate::MLD(val) => self.mld.update(val),
            ProgressUpdate::Remain(val) => {
                self.asg.nvar = val;
            }
        }
    }
}

impl Restarter {}

impl Export<(usize, usize, usize, usize), (RestartMode, usize)> for Restarter {
    /// exports:
    ///  1. the number of blocking in non-stabilization
    ///  1. the number of forcing restart non-stabilization
    ///  1. the index of span of stabilization phase
    ///  1. the number of stabilization flips
    ///
    ///```
    /// use crate::splr::{config::Config, solver::Restarter, types::*};
    /// let rst = Restarter::instantiate(&Config::default(), &CNFDescription::default());
    /// let (num_blk_non, num_stb_non, num_blk_stb, num_rst_stb) = rst.exports();
    /// let (rst_mode, num_stb) = rst.mode();
    ///```
    #[inline]
    fn exports(&self) -> (usize, usize, usize, usize) {
        (
            self.num_block,
            self.num_restart,
            self.stb.span(),
            self.stb.num_shift,
        )
    }
    fn mode(&self) -> (RestartMode, usize) {
        if self.stb.active {
            (RestartMode::Stabilize, self.stb.span())
        } else if self.luby.enable {
            (RestartMode::Luby, self.stb.span())
        } else {
            (RestartMode::Dynamic, self.stb.span())
        }
    }
}

#[cfg(not(progress_ACC))]
pub type RestarterEMAs<'a> = (&'a Ema2, &'a Ema2, &'a Ema2);
#[cfg(progress_ACC)]
pub type RestarterEMAs<'a> = (&'a Ema2, &'a Ema2, &'a Ema2, &'a Ema2);

impl<'a> ExportBox<'a, RestarterEMAs<'a>> for Restarter {
    #[cfg(not(progress_ACC))]
    fn exports_box(&'a self) -> Box<RestarterEMAs<'a>> {
        Box::from((&self.asg.ema, &self.lbd.ema, &self.mld.ema))
    }
    #[cfg(progress_ACC)]
    fn exports_box(&'a self) -> Box<RestarterEMAs<'a>> {
        Box::from((&self.acc.ema, &self.asg.ema, &self.lbd.ema, &self.mld.ema))
    }
}

#[derive(Debug)]
struct LubySeries {
    index: usize,
    seq: isize,
    size: usize,
}

impl Default for LubySeries {
    fn default() -> Self {
        LubySeries {
            index: 0,
            seq: 0,
            size: 1,
        }
    }
}

impl fmt::Display for LubySeries {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Luby[index:{}]", self.index)
    }
}

impl LubySeries {
    fn next(&mut self) -> Option<usize> {
        self.index += 1;
        let mut seq = self.seq;
        let mut size = self.size;
        while size < self.index + 1 {
            self.seq = seq;
            seq += 1;
            self.size = size;
            size = 2 * size + 1;
        }
        let mut index = self.index;
        while size - 1 != index {
            size = (size - 1) >> 1;
            seq -= 1;
            index %= size;
        }
        Some(2.0f64.powi(seq as i32) as usize)
    }
    fn reset(&mut self) {
        self.index = 0;
        self.seq = 0;
        self.size = 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ProgressLuby() {
        let mut luby = ProgressLuby {
            enable: true,
            active: true,
            step: 1,
            next_restart: 1,
            ..ProgressLuby::default()
        };
        luby.update(0);
        for v in vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8] {
            assert_eq!(luby.next_restart, v);
            luby.shift();
        }
    }
    #[test]
    fn test_LubySeries() {
        let mut luby = LubySeries::default();
        let v = vec![1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        let mut l: Vec<usize> = vec![];
        for _ in 1..15 {
            if let Some(x) = luby.next() {
                l.push(x);
            }
        }
        assert_eq!(l, v);
        // for v in vec![1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8] {
        //     if let Some(n) = luby.next() {
        //         assert_eq!(v, n);
        //     }
        // }
    }
}

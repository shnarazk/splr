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
    ACC(f64),
    ASG(usize),
    LBD(u16),
    Luby,
    MLD(u16),
    Reset,
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
    fn stabilize(&mut self, now: usize, progress: bool) -> Option<bool>;
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
}

impl Default for ProgressASG {
    fn default() -> ProgressASG {
        ProgressASG {
            enable: true,
            ema: Ema2::new(1),
            threshold: 1.4,
        }
    }
}

impl Instantiate for ProgressASG {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressASG {
            ema: Ema2::new(config.rst_asg_len).with_slow(config.rst_asg_slw),
            threshold: config.rst_asg_thr,
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
        self.ema.trend()
    }
}

impl ProgressEvaluator for ProgressASG {
    fn is_active(&self) -> bool {
        self.enable && self.threshold < self.ema.trend()
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
        self.ema
            .trend()
            .max(self.ema.get() * (self.num as f64) / (self.sum as f64))
    }
}

impl ProgressEvaluator for ProgressLBD {
    fn is_active(&self) -> bool {
        self.enable && self.threshold < self.ema.trend()
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
            ema: Ema2::new(10 * config.rst_lbd_len).with_slow(config.rst_lbd_slw),
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
        todo!();
    }
    fn shift(&mut self) {}
}

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

impl Instantiate for ProgressACC {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressACC {
            ema: Ema2::new(config.rst_lbd_len).with_slow(config.rst_lbd_slw),
            threshold: config.rst_ccc_thr,
            ..ProgressACC::default()
        }
    }
}

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
struct LubySeries {
    enable: bool,
    active: bool,
    index: usize,
    next_restart: usize,
    restart_inc: f64,
    step: usize,
}

impl Default for LubySeries {
    fn default() -> Self {
        const STEP: usize = 100;
        LubySeries {
            enable: false,
            active: false,
            index: 0,
            next_restart: STEP,
            restart_inc: 2.0,
            step: STEP,
        }
    }
}

impl Instantiate for LubySeries {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        LubySeries {
            enable: config.use_luby(),
            step: config.rst_step,
            ..LubySeries::default()
        }
    }
}

impl fmt::Display for LubySeries {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.enable {
            write!(f, "Luby[index:{}, step:{}]", self.index, self.next_restart,)
        } else {
            write!(f, "Luby(deactivated)")
        }
    }
}

impl EmaIF for LubySeries {
    type Input = usize;
    fn update(&mut self, index: usize) {
        if !self.enable {
            return;
        }
        if index == 0 {
            self.index = 0;
            self.next_restart = self.next_step();
            self.active = false;
        } else {
            self.active = self.next_restart < index;
        }
    }
    fn get(&self) -> f64 {
        self.next_restart as f64
    }
}

impl ProgressEvaluator for LubySeries {
    fn is_active(&self) -> bool {
        self.enable && self.active
    }
    fn shift(&mut self) {
        self.active = false;
        self.index += 1;
        self.next_restart = self.next_step();
    }
}

impl LubySeries {
    fn new(step: usize) -> Self {
        LubySeries {
            enable: true,
            active: false,
            index: 0,
            next_restart: step,
            restart_inc: 2.0,
            step,
        }
    }
}

/// Find the finite subsequence that contains index 'x', and the
/// size of that subsequence as: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8
impl LubySeries {
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
    num_active: usize,
    num_shift: usize,
    next_trigger: usize,
    restart_inc: f64,
    step: usize,
    luby: LubySeries,
}

impl Default for GeometricStabilizer {
    fn default() -> Self {
        GeometricStabilizer {
            enable: true,
            active: false,
            num_active: 0,
            num_shift: 0,
            next_trigger: 1000,
            restart_inc: 2.0,
            step: 1000,
            luby: LubySeries::new(1000),
        }
    }
}

impl Instantiate for GeometricStabilizer {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        GeometricStabilizer {
            enable: config.use_stabilize(),
            restart_inc: config.rst_stb_scl,
            ..GeometricStabilizer::default()
        }
    }
}

impl fmt::Display for GeometricStabilizer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.enable {
            write!(f, "Stabilizer(dead)")
        } else if self.active && self.enable {
            write!(f, "Stabilizer[+{}]", self.next_trigger)
        } else {
            write!(f, "Stabilizer[-{}]", self.next_trigger)
        }
    }
}

impl GeometricStabilizer {
    fn update(&mut self, now: usize) -> bool {
        if self.enable && self.next_trigger <= now {
            self.active = !self.active;
            if self.active {
                self.num_active += 1;
            }
            self.luby.shift();
            self.step = self.luby.next_restart;
            self.next_trigger = now + self.step;
            self.num_shift += 1;
            true
        } else {
            false
        }
    }
    fn span(&self) -> usize {
        self.step / 1000
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
    acc: ProgressACC,
    asg: ProgressASG,
    // bkt: ProgressBucket,
    lbd: ProgressLBD,
    mld: ProgressMLD,
    // pub rcc: ProgressRCC,
    // pub blvl: ProgressLVL,
    // pub clvl: ProgressLVL,
    luby: LubySeries,
    stb: GeometricStabilizer,
    after_restart: usize,
    restart_step: usize,
    initial_restart_step: usize,
    progress_this_phase: bool,
    progress_last_phase: bool,

    //
    //## statistics
    //
    num_block_non_stabilized: usize,
    num_restart_non_stabilized: usize,
    num_block_stabilized: usize,
    num_restart_stabilized: usize,
}

impl Default for Restarter {
    fn default() -> Restarter {
        Restarter {
            acc: ProgressACC::default(),
            asg: ProgressASG::default(),
            // bkt: ProgressBucket::default(),
            lbd: ProgressLBD::default(),
            mld: ProgressMLD::default(),
            // rcc: ProgressRCC::default(),
            // blvl: ProgressLVL::default(),
            // clvl: ProgressLVL::default(),
            luby: LubySeries::default(),
            stb: GeometricStabilizer::default(),
            after_restart: 0,
            restart_step: 0,
            initial_restart_step: 0,
            progress_this_phase: false,
            progress_last_phase: true,
            num_block_non_stabilized: 0,
            num_restart_non_stabilized: 0,
            num_block_stabilized: 0,
            num_restart_stabilized: 0,
        }
    }
}

impl Instantiate for Restarter {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Self {
        Restarter {
            acc: ProgressACC::instantiate(config, cnf),
            asg: ProgressASG::instantiate(config, cnf),
            // bkt: ProgressBucket::instantiate(config, cnf),
            lbd: ProgressLBD::instantiate(config, cnf),
            mld: ProgressMLD::instantiate(config, cnf),
            // rcc: ProgressRCC::instantiate(config, cnf),
            // blvl: ProgressLVL::instantiate(config, cnf),
            // clvl: ProgressLVL::instantiate(config, cnf),
            luby: LubySeries::instantiate(config, cnf),
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
            SolverEvent::Stabilize(true) => (),
            SolverEvent::Stabilize(false) => (),
            _ => (),
        }
    }
}

/// Type for the result of `restart`.
pub enum RestartDecision {
    /// We should block restart
    Block,
    /// We should block restart in stabilization mode
    Cancel,
    /// We should restart now
    Force,
    /// TODO
    Postpone,
    /// We should restart now in stabilization mode
    Stabilize,
}

impl RestartIF for Restarter {
    #[inline]
    #[allow(clippy::collapsible_if)]
    fn restart(&mut self) -> Option<RestartDecision> {
        if self.luby.is_active() {
            self.luby.shift();
            self.after_restart = 0;
            return Some(RestartDecision::Force);
        }
        if self.after_restart < self.restart_step {
            return None;
        }
        self.acc.shift();
        if self.stb.active {
            return Some(RestartDecision::Postpone);
        }

        // Branching based on sizes of learnt clauses comparing with the average of
        // maximum LBDs used in conflict analyzsis.
        let _good_path = self.progress_last_phase
            && self.lbd.get()
                < self.mld.get() + self.stb.span() as f64 * self.mld.scaling + self.mld.threshold;

        if self.asg.is_active() /* && good_path */ {
            self.after_restart = 0;
            self.num_block_non_stabilized += 1;
            return Some(RestartDecision::Block);
        }
        // if self.lbd.is_active() && !good_path {
        let offset = 0.5 / (self.stb.span() as f64 + 1.0).log(2.0);
        if self.lbd.threshold * (1.0 + offset) < self.lbd.trend() {
            self.after_restart = 0;
            self.num_restart_non_stabilized += 1;
            self.progress_this_phase = true;
            return Some(RestartDecision::Force);
        }
        Some(RestartDecision::Postpone)
    }
    fn stabilize(&mut self, now: usize, progress: bool) -> Option<bool> {
        let toggle = self.stb.update(now);
        if toggle && !self.stb.active {
            self.progress_last_phase = self.progress_this_phase || progress || self.stb.span() < 10;
            self.progress_this_phase = false;
        }
        if toggle {
            Some(self.stb.active)
        } else {
            None
        }
    }
    fn update(&mut self, kind: ProgressUpdate) {
        match kind {
            ProgressUpdate::Counter => {
                self.after_restart += 1;
                self.luby.update(self.after_restart);
            }
            ProgressUpdate::ACC(fval) => self.acc.update(fval),
            ProgressUpdate::ASG(val) => self.asg.update(val),
            ProgressUpdate::LBD(val) => self.lbd.update(val),
            ProgressUpdate::Luby => self.luby.update(0),
            ProgressUpdate::MLD(val) => self.mld.update(val),
            ProgressUpdate::Reset => (),
        }
    }
}

impl Restarter {}

impl Export<(usize, usize, usize, usize), (RestartMode, usize)> for Restarter {
    /// exports:
    ///  1. the number of blocking in non-stabilization
    ///  1. the number of forcing restart non-stabilization
    ///  1. the number of blocking in stabilization
    ///  1. the number of forcing in stabilization
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
            self.num_block_non_stabilized,
            self.num_restart_non_stabilized,
            self.num_block_stabilized,
            self.num_restart_stabilized,
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
    fn stabilization_length(&self) -> (usize, usize, f64, f64) {
        (
            self.stb.span(),
            self.stb.num_shift,
            self.mld.threshold,
            self.mld.scaling,
        )
    }
}

impl<'a> ExportBox<'a, (&'a Ema2, &'a Ema2, &'a Ema2, &'a Ema2)> for Restarter {
    fn exports_box(&'a self) -> Box<(&'a Ema2, &'a Ema2, &'a Ema2, &'a Ema2)> {
        Box::from((&self.acc.ema, &self.asg.ema, &self.lbd.ema, &self.mld.ema))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_luby_series() {
        let mut luby = LubySeries {
            enable: true,
            active: true,
            step: 1,
            ..LubySeries::default()
        };
        luby.update(0);
        for v in vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8] {
            assert_eq!(luby.next_restart, v);
            luby.shift();
        }
    }
}

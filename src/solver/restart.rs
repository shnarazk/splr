//! Crate `restart` provides restart heuristics.
use {
    crate::{solver::SolverEvent, types::*},
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
    ASG(usize),
    LBD(u16),
    Counter,

    #[cfg(feature = "Luby_restart")]
    Luby,

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
}

/// API for [`restart`](`crate::solver::RestartIF::restart`) and [`stabilize`](`crate::solver::RestartIF::stabilize`).
pub trait RestartIF {
    /// check blocking and forcing restart condition.
    fn restart(&mut self) -> Option<RestartDecision>;
    /// check stabilization mode and  return:
    /// - `Some(parity_bit, just_start_a_new_cycle)` if a stabilization phase has just ended.
    /// - `None` otherwise.
    fn stabilize(&mut self) -> Option<bool>;
    /// update specific sub-module
    fn update(&mut self, kind: ProgressUpdate);
}

/// An assignment history used for blocking restart.
#[derive(Clone, Debug)]
struct ProgressASG {
    enable: bool,
    ema: Ema2,
    /// For block restart based on average assignments: 1.40.
    /// This is called `R` in Glucose
    threshold: f64,
    num_var: usize,
}

impl Default for ProgressASG {
    fn default() -> ProgressASG {
        ProgressASG {
            enable: true,
            ema: Ema2::new(1),
            threshold: 1.4,
            num_var: 1,
        }
    }
}

impl Instantiate for ProgressASG {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Self {
        ProgressASG {
            ema: Ema2::new(config.rst_asg_len).with_slow(config.rst_asg_slw),
            threshold: config.rst_asg_thr,
            num_var: cnf.num_of_variables,
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
        let nv = self.num_var as f64;
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
#[derive(Clone, Debug)]
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

/// An implementation of Luby series.
#[derive(Clone, Debug)]
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
    type Input = usize;
    fn update(&mut self, now: usize) {
        if !self.enable {
            return;
        }
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
        self.next_restart = self.step * self.luby.next();
    }
}

/// An implementation of CaDiCaL-style blocker.
/// This is a stealth blocker between the other evaluators and solver;
/// the other evaluators work as if this blocker doesn't exist.
/// When an evaluator becomes active, we accept and shift it. But this blocker
/// absorbs not only the forcing signal but also blocking signal.
/// This exists in macro `reset`.
#[derive(Clone, Debug)]
struct GeometricStabilizer {
    enable: bool,
    longest_span: usize,
    luby: LubySeries,
    num_cycle: usize,
    num_shift: usize,
    next_trigger: usize,
    reset_requested: bool,
    step: usize,
}

impl Default for GeometricStabilizer {
    fn default() -> Self {
        GeometricStabilizer {
            #[cfg(not(feature = "Luby_stabilization"))]
            enable: false,
            #[cfg(feature = "Luby_stabilization")]
            enable: true,

            longest_span: 1,
            luby: LubySeries::default(),
            num_cycle: 0,
            num_shift: 0,
            next_trigger: 1,
            reset_requested: false,
            step: 1,
        }
    }
}

impl Instantiate for GeometricStabilizer {
    fn instantiate(_config: &Config, _: &CNFDescription) -> Self {
        GeometricStabilizer::default()
    }
}

impl fmt::Display for GeometricStabilizer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.enable {
            write!(f, "Stabilizer(dead)")
        } else if self.enable {
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
    fn update(&mut self, now: usize) -> Option<bool> {
        if self.enable && self.next_trigger <= now {
            self.num_shift += 1;
            let mut new_cycle: bool = false;
            if self.longest_span < self.step {
                new_cycle = true;
                self.num_cycle += 1;
                self.longest_span = self.step;
                if self.reset_requested {
                    self.luby.reset();
                    self.longest_span = 1;
                    self.step = self.luby.next();
                    self.reset_requested = false;
                    self.next_trigger = now;
                }
            }
            self.step = self.luby.next();
            self.next_trigger = now + self.longest_span / self.step;
            return Some(new_cycle);
        }
        None
    }
}

/// `Restarter` provides restart API and holds data about restart conditions.
#[derive(Clone, Debug)]
pub struct Restarter {
    asg: ProgressASG,
    lbd: ProgressLBD,
    // pub blvl: ProgressLVL,
    // pub clvl: ProgressLVL,
    luby: ProgressLuby,
    stb: GeometricStabilizer,
    after_restart: usize,
    restart_step: usize,
    restart_waiting: usize,
    initial_restart_step: usize,
    stb_expansion_factor: f64,

    //
    //## statistics
    //
    num_block: usize,
    num_restart: usize,
}

impl Default for Restarter {
    fn default() -> Restarter {
        Restarter {
            asg: ProgressASG::default(),
            lbd: ProgressLBD::default(),
            // blvl: ProgressLVL::default(),
            // clvl: ProgressLVL::default(),
            luby: ProgressLuby::default(),
            stb: GeometricStabilizer::default(),
            after_restart: 0,
            restart_step: 0,
            restart_waiting: 0,
            initial_restart_step: 0,
            stb_expansion_factor: 1.0,

            num_block: 0,
            num_restart: 0,
        }
    }
}

impl Instantiate for Restarter {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Self {
        Restarter {
            asg: ProgressASG::instantiate(config, cnf),
            lbd: ProgressLBD::instantiate(config, cnf),
            // blvl: ProgressLVL::instantiate(config, cnf),
            // clvl: ProgressLVL::instantiate(config, cnf),
            luby: ProgressLuby::instantiate(config, cnf),
            stb: GeometricStabilizer::instantiate(config, cnf),
            restart_step: config.rst_step,
            initial_restart_step: config.rst_step,
            stb_expansion_factor: config.rst_stb_exp,

            ..Restarter::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        match e {
            SolverEvent::Assert(_) => {
                self.stb.reset_requested = true;
                self.restart_waiting = self.stb.step;
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
}

impl RestartIF for Restarter {
    fn restart(&mut self) -> Option<RestartDecision> {
        if self.luby.is_active() {
            self.luby.shift();
            return Some(RestartDecision::Force);
        }
        if self.after_restart < self.restart_step {
            return None;
        }

        if self.asg.is_active() {
            self.num_block += 1;
            self.restart_waiting = 0;
            self.after_restart = 0;
            return Some(RestartDecision::Block);
        }
        if self.lbd.is_active() {
            self.restart_waiting += 1;
            if self.stb.step <= self.restart_waiting {
                self.restart_waiting = 0;
                return Some(RestartDecision::Force);
            }
            self.after_restart = 0;
        }
        None
    }
    #[cfg(feature = "Luby_stabilization")]
    fn stabilize(&mut self) -> Option<bool> {
        self.stb.update(self.num_restart + self.num_block)
    }
    #[cfg(not(feature = "Luby_stabilization"))]
    fn stabilize(&mut self) -> Option<bool> {
        Some(false)
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

            ProgressUpdate::Remain(val) => {
                self.asg.num_var = val;
            }
        }
    }
}

pub mod property {
    use super::Restarter;
    use crate::types::*;

    #[derive(Clone, Debug, PartialEq)]
    pub enum Tusize {
        NumBlock,
        NumCycle,
        NumRestart,
        NumStage,
        SpanLen,
    }

    impl PropertyDereference<Tusize, usize> for Restarter {
        #[inline]
        fn derefer(&self, k: Tusize) -> usize {
            match k {
                Tusize::NumBlock => self.num_block,
                Tusize::NumCycle => self.stb.num_cycle,
                Tusize::NumRestart => self.num_restart,
                Tusize::NumStage => self.stb.num_shift,
                Tusize::SpanLen => self.stb.step,
            }
        }
    }

    #[derive(Clone, Debug, PartialEq)]
    pub enum TEma2 {
        ASG,
        LBD,
    }

    impl PropertyReference<TEma2, Ema2> for Restarter {
        #[inline]
        fn refer(&self, k: TEma2) -> &Ema2 {
            match k {
                TEma2::ASG => &self.asg.ema,
                TEma2::LBD => &self.lbd.ema,
            }
        }
    }
}

#[derive(Clone, Debug)]
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
    /// Find the finite subsequence that contains index 'x', and the
    /// size of that subsequence as: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8
    fn next(&mut self) -> usize {
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
        2usize.pow(seq as u32)
    }
    #[allow(dead_code)]
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
    fn test_progress_luby() {
        let mut luby = ProgressLuby {
            enable: true,
            active: true,
            step: 1,
            next_restart: 1,
            ..ProgressLuby::default()
        };
        luby.update(0);
        for v in vec![
            1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1,
        ] {
            assert_eq!(luby.next_restart, v);
            luby.shift();
        }
    }
    #[test]
    fn test_luby_series() {
        let mut luby = LubySeries::default();
        let v = vec![1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        let mut l: Vec<usize> = vec![];
        for _ in 1..15 {
            l.push(luby.next());
        }
        assert_eq!(l, v);
    }
}

/// Crate `restart` provides restart heuristics.
use {
    crate::{
        config::Config,
        state::{SearchStrategy, State},
        types::*,
    },
    std::fmt,
};

/// API for restart condition.
trait ProgressEvaluator {
    /// map the value into a bool for forcing/blocking restart.
    fn is_active(&self) -> bool;
}

/// Submodule index to access them indirectly.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RestarterModule {
    Counter = 0,
    ASG,
    LBD,
    Luby,
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

/// API for restart like `block_restart`, `force_restart` and so on.
pub trait RestartIF {
    /// block restart if needed.
    fn block_restart(&mut self) -> bool;
    /// force restart if needed.
    fn force_restart(&mut self) -> bool;
    /// update specific submodule
    fn update(&mut self, kind: RestarterModule, val: usize);
}

/// An assignment history used for blocking restart.
#[derive(Debug)]
pub struct ProgressASG {
    asg: usize,
    ema: Ema,
    /// For block restart based on average assignments: 1.40.
    /// This is called `R` in Glucose
    threshold: f64,
}

impl Instantiate for ProgressASG {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressASG {
            ema: Ema::new(config.restart_asg_len),
            asg: 0,
            threshold: config.restart_blocking,
        }
    }
}

impl EmaIF for ProgressASG {
    type Input = usize;
    fn update(&mut self, n: usize) {
        self.asg = n;
        self.ema.update(n as f64);
    }
    fn get(&self) -> f64 {
        self.ema.get()
    }
    fn trend(&self) -> f64 {
        (self.asg as f64) / self.ema.get()
    }
}

impl ProgressEvaluator for ProgressASG {
    fn is_active(&self) -> bool {
        self.threshold * self.ema.get() < (self.asg as f64)
    }
}

/// An EMA of learnt clauses' LBD, used for forcing restart.
#[derive(Debug)]
pub struct ProgressLBD {
    ema: Ema2,
    num: usize,
    sum: usize,
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glucose
    threshold: f64,
}

impl Instantiate for ProgressLBD {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressLBD {
            ema: Ema2::new(config.restart_lbd_len).with_slow(4 * config.restart_lbd_len),
            num: 0,
            sum: 0,
            threshold: config.restart_threshold,
        }
    }
}

impl EmaIF for ProgressLBD {
    type Input = usize;
    fn update(&mut self, d: usize) {
        self.num += 1;
        self.sum += d;
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
        (self.sum as f64) < self.ema.get() * (self.num as f64) * self.threshold
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
}

/// An EMA of reccuring conflict complexity (unused now).
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
}

/// An implementation of Luby series.
#[derive(Debug)]
pub struct LubySeries {
    active: bool,
    index: usize,
    next_restart: usize,
    restart_inc: f64,
    step: usize,
}

impl Default for LubySeries {
    fn default() -> Self {
        LubySeries {
            active: false,
            index: 0,
            next_restart: 0,
            restart_inc: 2.0,
            step: 100,
        }
    }
}

impl Instantiate for LubySeries {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        LubySeries {
            step: config.restart_step,
            ..LubySeries::default()
        }
    }
}

impl fmt::Display for LubySeries {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.active {
            write!(f, "Luby[index:{}, step:{}]", self.index, self.next_restart,)
        } else {
            write!(f, "Luby(deactive)")
        }
    }
}

impl EmaIF for LubySeries {
    type Input = usize;
    fn update(&mut self, reset: usize) {
        debug_assert!(self.active);
        if reset == 0 {
            self.index = 0;
        } else {
            self.index += 1;
        }
        self.next_restart = self.next_step();
    }
    fn get(&self) -> f64 {
        self.next_restart as f64
    }
}

impl ProgressEvaluator for LubySeries {
    fn is_active(&self) -> bool {
        todo!()
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

/// An implementation of Cadical-style blocker.
#[derive(Debug)]
pub struct GeometricBlocker {
    enable: bool,
    active: bool,
    next_trigger: usize,
    restart_inc: f64,
}

impl Default for GeometricBlocker {
    fn default() -> Self {
        GeometricBlocker {
            enable: true,
            active: false,
            next_trigger: 1000,
            restart_inc: 2.0,
        }
    }
}

impl Instantiate for GeometricBlocker {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        GeometricBlocker {
            enable: !config.without_stab,
            ..GeometricBlocker::default()
        }
    }
}

impl fmt::Display for GeometricBlocker {
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

impl EmaIF for GeometricBlocker {
    type Input = usize;
    fn update(&mut self, now: usize) {
        if self.enable && self.next_trigger <= now {
            self.active = !self.active;
            self.next_trigger = ((now as f64) * self.restart_inc) as usize;
        }
    }
    fn get(&self) -> f64 {
        todo!()
    }
}

impl ProgressEvaluator for GeometricBlocker {
    fn is_active(&self) -> bool {
        self.active
    }
}

/// `Restarter` provides restart API and holds data about restart conditions.
#[derive(Debug)]
pub struct Restarter {
    asg: ProgressASG,
    blk: GeometricBlocker,
    lbd: ProgressLBD,
    // pub rcc: ProgressRCC,
    // pub blvl: ProgressLVL,
    // pub clvl: ProgressLVL,
    luby: LubySeries,
    after_restart: usize,
    next_restart: usize,
    restart_step: usize,

    //
    //## statistics
    //
    num_block: usize,
}

impl Instantiate for Restarter {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Self {
        Restarter {
            asg: ProgressASG::instantiate(config, cnf),
            blk: GeometricBlocker::instantiate(config, cnf),
            lbd: ProgressLBD::instantiate(config, cnf),
            // rcc: ProgressRCC::instantiate(config, cnf),
            // blvl: ProgressLVL::instantiate(config, cnf),
            // clvl: ProgressLVL::instantiate(config, cnf),
            luby: LubySeries::instantiate(config, cnf),
            after_restart: 0,
            next_restart: 100,
            restart_step: config.restart_step,
            num_block: 0,
        }
    }
    fn adapt_to(&mut self, state: &State, num_conflict: usize) {
        if !self.luby.active && state.config.with_deep_search {
            if state.stagnated {
                self.restart_step = state.reflection_interval;
                self.next_restart += state.reflection_interval;
            } else {
                self.restart_step = state.config.restart_step;
            }
        }
        match state.strategy {
            (SearchStrategy::Initial, _) => (),
            (SearchStrategy::LowSuccesiveLuby, n) => {
                if n == num_conflict {
                    self.luby.active = true;
                }
            }
            // SearchStrategy::HighSuccesive => (),
            // SearchStrategy::LowSuccesiveM => (),
            // SearchStrategy::ManyGlues => (),
            // SearchStrategy::Generic => (),
            _ => {
                // self.luby.active = state.c_lvl.get() < 14.0;
            }
        }
    }
}

macro_rules! reset {
    ($executor: expr) => {
        $executor.after_restart = 0;
        return true;
    };
}

impl RestartIF for Restarter {
    fn block_restart(&mut self) -> bool {
        if 100 < self.lbd.num
            && !self.luby.active
            && !self.blk.active
            && self.restart_step <= self.after_restart
            && self.asg.is_active()
        {
            self.num_block += 1;
            reset!(self);
        }
        false
    }
    fn force_restart(&mut self) -> bool {
        if self.luby.active {
            if self.luby.next_restart <= self.after_restart {
                self.luby.update(1);
                reset!(self);
            }
        } else if self.blk.active {
            return false;
        } else if self.restart_step <= self.after_restart && self.lbd.is_active() {
            reset!(self);
        }
        false
    }
    fn update(&mut self, kind: RestarterModule, val: usize) {
        match kind {
            RestarterModule::Counter => {
                // use an embeded value, expecting compile time optimization
                self.after_restart += 1;
                self.blk.update(val);
            }
            RestarterModule::ASG => {
                self.asg.update(val);
            }
            RestarterModule::LBD => {
                self.lbd.update(val);
            }
            RestarterModule::Luby => {
                if self.luby.active {
                    // use an embeded value, expecting compile time optimization
                    self.luby.update(0);
                }
            }
        }
    }
}

impl Export<(RestartMode, usize, f64, f64, f64)> for Restarter {
    ///```
    /// let (rst_mode, rst_num_block, rst_asg_trend, rst_lbd_get, rst_lbd_trend) = rst.exports();
    ///```
    #[inline]
    fn exports(&self) -> (RestartMode, usize, f64, f64, f64) {
        (
            if self.blk.active {
                RestartMode::Stabilize
            } else if self.luby.active {
                RestartMode::Luby
            } else {
                RestartMode::Dynamic
            },
            self.num_block,
            self.asg.trend(),
            self.lbd.get(),
            self.lbd.trend(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_luby_series() {
        let mut luby = LubySeries {
            active: true,
            step: 1,
            ..LubySeries::default()
        };
        luby.update(0);
        for v in vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8] {
            assert_eq!(luby.next_restart, v);
            luby.update(1);
        }
    }
}

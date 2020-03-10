/// Crate `restart` provides restart heuristics.
use {
    crate::{config::Config, state::{SearchStrategy, State}, types::*},
    std::fmt,
};

/// API for restart condition.
trait ProgressEvaluator {
    /// map the value into a bool for forcing/blocking restart.
    fn is_active(&self) -> bool;
}

/// API for restart like `block_restart`, `force_restart` and so on.
pub trait RestartIF {
    /// block restart if needed.
    fn block_restart(&mut self) -> bool;
    /// force restart if needed.
    fn force_restart(&mut self) -> bool;
}

/// An assignment history used for blocking restart
#[derive(Debug)]
pub struct ProgressASG {
    asg: usize,
    ema: Ema,
    /// For block restart based on average assignments: 1.40.
    /// This is called `R` in Glucose
    pub threshold: f64,
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

/// An EMA of learnt clauses' LBD, used for forcing restart
#[derive(Debug)]
pub struct ProgressLBD {
    ema: Ema2,
    num: usize,
    sum: usize,
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glucose
    pub threshold: f64,
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
pub struct ProgressLVL {
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

/// An EMA of reccuring conflict complexity (unused now)
#[derive(Debug)]
struct ProgressRCC {
    pub heat: Ema2,
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
    pub active: bool,
    pub index: usize,
    next_restart: usize,
    restart_inc: f64,
    pub step: usize,
}

impl Default for LubySeries {
    fn default() -> Self {
        LubySeries {
            active: false,
            index: 0,
            next_restart: 0,
            restart_inc: 2.0,
            step: 10,
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

/// `Restarter` provides restart API and holds data about restart conditions.
#[derive(Debug)]
pub struct Restarter {
    pub asg: ProgressASG,
    pub lbd: ProgressLBD,
    // pub rcc: ProgressRCC,
    pub blvl: ProgressLVL,
    pub clvl: ProgressLVL,
    pub luby: LubySeries,
    pub after_restart: usize,
    pub next_restart: usize,
    pub restart_step: usize,
}

impl Instantiate for Restarter {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> Self {
        Restarter {
            asg: ProgressASG::instantiate(config, cnf),
            lbd: ProgressLBD::instantiate(config, cnf),
            // rcc: ProgressRCC::instantiate(config, cnf),
            blvl: ProgressLVL::instantiate(config, cnf),
            clvl: ProgressLVL::instantiate(config, cnf),
            luby: LubySeries::instantiate(config, cnf),
            after_restart: 0,
            next_restart: 100,
            restart_step: config.restart_step,
        }
    }
    fn adapt_to(&mut self, state: &State) {
        match state.strategy {
            SearchStrategy::Initial => (),
            SearchStrategy::Generic => (),
            SearchStrategy::LowDecisions => {
                // self.lbd.threshold = 0.5 * self.lbd.threshold + 0.5;
            }
            SearchStrategy::HighSuccesive => (),
            SearchStrategy::LowSuccesiveLuby => {
                self.luby.active = true;
                self.luby.step = 100;
            }
            SearchStrategy::LowSuccesiveM => (),
            SearchStrategy::ManyGlues => (),
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
            && self.restart_step <= self.after_restart
            && self.asg.is_active()
        {
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
        } else if self.restart_step <= self.after_restart && self.lbd.is_active() {
            reset!(self);
        }
        false
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

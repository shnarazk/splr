use crate::config::Config;
use crate::traits::*;

// const RESET_EMA: usize = 400;

/// Exponential Moving Average w/ a calibrator
#[derive(Debug)]
pub struct Ema {
    val: f64,
    cal: f64,
    sca: f64,
}

impl EmaIF for Ema {
    fn new(s: usize) -> Ema {
        Ema {
            val: 0.0,
            cal: 0.0,
            sca: 1.0 / (s as f64),
        }
    }
    fn update(&mut self, x: f64) {
        self.val = self.sca * x + (1.0 - self.sca) * self.val;
        self.cal = self.sca + (1.0 - self.sca) * self.cal;
    }
    fn get(&self) -> f64 {
        self.val / self.cal
    }
}

#[derive(Debug)]
pub struct ProgressASG {
    asg: usize,
    ema: Ema,
    /// For block restart based on average assignments: 1.40.
    /// This is called `R` in Glucose
    pub threshold: f64,
}

impl ProgressEvaluator for ProgressASG {
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
    fn is_active(&self) -> bool {
        self.threshold * self.ema.get() < (self.asg as f64)
    }
    fn new(config: &Config) -> Self {
        ProgressASG {
            ema: Ema::new(config.restart_asg_len),
            asg: 0,
            threshold: config.restart_blocking,
        }
    }
}

#[derive(Debug)]
pub struct ProgressLBD {
    ema: Ema,
    num: usize,
    sum: usize,
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glucose
    pub threshold: f64,
}

impl ProgressEvaluator for ProgressLBD {
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
        self.ema.get() * (self.num as f64) / (self.sum as f64)
    }
    fn is_active(&self) -> bool {
        (self.sum as f64) < self.ema.get() * (self.num as f64) * self.threshold
    }
    fn new(config: &Config) -> Self {
        ProgressLBD {
            ema: Ema::new(config.restart_lbd_len),
            num: 0,
            sum: 0,
            threshold: config.restart_threshold,
        }
    }
}

// Restart stat
#[derive(Debug)]
pub struct RestartExecutor {
    pub adaptive_restart: bool,
    pub asg: ProgressASG,
    pub lbd: ProgressLBD,
    pub use_luby_restart: bool,
    pub after_restart: usize,
    pub cur_restart: usize,
    pub next_restart: usize,
    pub restart_step: usize,
    luby_count: f64,
    pub luby_restart_num_conflict: f64,
    pub luby_restart_inc: f64,
    pub luby_current_restart: usize,
    pub luby_restart_factor: f64,
}

impl RestartIF for RestartExecutor {
    fn new(config: &Config) -> Self {
        RestartExecutor {
            adaptive_restart: !config.without_adaptive_restart,
            asg: ProgressASG::new(config),
            lbd: ProgressLBD::new(config),
            use_luby_restart: false,
            after_restart: 0,
            cur_restart: 1,
            next_restart: 100,
            restart_step: config.restart_step,
            luby_count: 0.0,
            luby_restart_num_conflict: 0.0,
            luby_restart_inc: 2.0,
            luby_current_restart: 0,
            luby_restart_factor: 100.0,
        }
    }
    fn block_restart(&mut self) -> bool {
        if 100 < self.lbd.num
            && !self.use_luby_restart
            && self.restart_step <= self.after_restart
            && self.asg.is_active()
        {
            self.after_restart = 0;
            return true;
        }
        false
    }
    fn force_restart(&mut self) -> bool {
        if (self.use_luby_restart && self.luby_restart_num_conflict <= self.luby_count)
            || (!self.use_luby_restart
                && self.restart_step <= self.after_restart
                && self.lbd.is_active())
        {
            self.after_restart = 0;
            if self.use_luby_restart {
                self.luby_count = 0.0;
                self.luby_current_restart += 1;
                self.luby_restart_num_conflict =
                    luby(self.luby_restart_inc, self.luby_current_restart)
                        * self.luby_restart_factor;
            }
            return true;
        }
        false
    }
    fn initialize_luby(&mut self) {
        if self.use_luby_restart {
            self.luby_restart_num_conflict =
                luby(self.luby_restart_inc, self.luby_current_restart) * self.luby_restart_factor;
            self.luby_count = 0.0;
        }
    }
    fn update_luby(&mut self) {
        if self.use_luby_restart {
            self.luby_count += 1.0;
        }
    }
}

/// Find the finite subsequence that contains index 'x', and the
/// size of that subsequence:
fn luby(y: f64, mut x: usize) -> f64 {
    let mut size: usize = 1;
    let mut seq: usize = 0;
    // for(size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1);
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    // while(size - 1 != x) {
    //     size = (size - 1) >> 1;
    //     seq--;
    //     x = x % size;
    // }
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    // return pow(y, seq);
    y.powf(seq as f64)
}

/// Exponential Moving Average pair
struct Ema2 {
    fast: f64,
    slow: f64,
    calf: f64,
    cals: f64,
    fe: f64,
    se: f64,
}

impl EmaIF for Ema2 {
    fn new(f: usize) -> Ema2 {
        Ema2 {
            fast: 0.0,
            slow: 0.0,
            calf: 0.0,
            cals: 0.0,
            fe: 1.0 / (f as f64),
            se: 1.0 / (f as f64),
        }
    }
    fn get(&self) -> f64 {
        self.fast / self.calf
    }
    fn update(&mut self, x: f64) {
        self.fast = self.fe * x + (1.0 - self.fe) * self.fast;
        self.slow = self.se * x + (1.0 - self.se) * self.slow;
        self.calf = self.fe + (1.0 - self.fe) * self.calf;
        self.cals = self.se + (1.0 - self.se) * self.cals;
    }
    fn reset(&mut self) {
        self.slow = self.fast;
        self.cals = self.calf;
    }
}

impl Ema2 {
    #[allow(dead_code)]
    fn rate(&self) -> f64 {
        self.fast / self.slow * (self.cals / self.calf)
    }
    #[allow(dead_code)]
    fn with_slow(mut self, s: u64) -> Ema2 {
        self.se = 1.0 / (s as f64);
        self
    }
}

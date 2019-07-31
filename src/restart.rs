use crate::propagator::AssignStack;
use crate::state::{Stat, State};
use crate::traits::*;
use crate::var::VarDB;

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

impl RestartIF for State {
    /// return true to forcing restart. Otherwise false.
    fn restart(&mut self, asgs: &AssignStack, _vdb: &mut VarDB, luby_count: &mut f64) -> bool {
        let _ncnfl = self.stats[Stat::Conflict];
        let _nas = asgs.len();
        // polar parameters
        let _epsilon = 0.05;
        // first, handle Luby path
        if self.use_luby_restart {
            if self.luby_restart_num_conflict <= *luby_count {
                self.stats[Stat::LubyRestart] += 1;
                self.after_restart = 0;
                *luby_count = 0.0;
                self.luby_current_restarts += 1;
                self.luby_restart_num_conflict =
                    luby(self.luby_restart_inc, self.luby_current_restarts)
                        * self.luby_restart_factor;
                return true;
            }
            if 0.8 < self.ema_pv_inc.ratio()
                && 4.0 * self.ema_lbd.get() < self.c_lvl.get()
            {
                self.use_luby_restart = false;
            }
            return false;
        }
        if self.after_restart < self.restart_step {
            return false;
        }
/*
        if (self.num_vars - self.num_eliminated_vars < 2 * self.num_polar_vars
            || self.ema_pv_inc.get() < 0.0001)
            && self.ema_pv_inc.ratio() < 0.5
            && (self.ema_lbd.get() - self.b_lvl.get()).abs() < 1.0
        {
            self.use_luby_restart = true;
            return true;
        }
        // check invoking condition
        let ave = self.stats[Stat::SumLBD] as f64 / ncnfl as f64;
        if false && ave < self.ema_lbd.get() * self.restart_thr {
            self.stats[Stat::Restart] += 1;
            self.ema_restart_len.update(self.after_restart as f64);
            self.after_restart = 0;
            return true;
        }
*/
/*
        // check blocking condition
        if self.restart_blk * self.ema_asg.get() < nas as f64 {
            self.after_restart = 0;
            self.stats[Stat::BlockRestart] += 1;
            return false;
        }
*/
        false
    }
    fn restart_update_lbd(&mut self, lbd: usize) {
        self.ema_lbd.update(lbd as f64);
        self.after_restart += 1;
    }
    fn restart_update_asg(&mut self, n: usize) {
        self.ema_asg.update(n as f64);
        // self.sum_asg += n as f64 / config.num_vars as f64;
    }
    fn restart_update_luby(&mut self) {
        if self.use_luby_restart {
            self.luby_restart_num_conflict =
                luby(self.luby_restart_inc, self.luby_current_restarts) * self.luby_restart_factor;
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
#[derive(Debug)]
pub struct Ema2 {
    fast: f64,
    slow: f64,
    calf: f64,
    cals: f64,
    fe: f64,
    se: f64,
}

impl EmaIF for Ema2 {
    fn new(s: usize) -> Ema2 {
        Ema2 {
            fast: 0.0,
            slow: 0.0,
            calf: 0.0,
            cals: 0.0,
            fe: 1.0 / (s as f64),
            se: 1.0 / (s as f64),
        }
    }
    fn get(&self) -> f64 {
        self.slow / self.cals
    }
    fn update(&mut self, x: f64) {
        self.fast = self.fe * x + (1.0 - self.fe) * self.fast;
        self.slow = self.se * x + (1.0 - self.se) * self.slow;
        self.calf = self.fe + (1.0 - self.fe) * self.calf;
        self.cals = self.se + (1.0 - self.se) * self.cals;
    }
    fn reset(&mut self) {
        self.fast = self.slow;
        self.calf = self.cals;
    }
}

impl Ema2 {
    pub fn get_fast(&self) -> f64 {
        self.fast / self.calf
    }
    pub fn ratio(&self) -> f64 {
        self.fast / self.slow * (self.cals / self.calf)
    }
    pub fn with_fast(mut self, f: u64) -> Self {
        self.fe = 1.0 / (f as f64);
        self
    }
    pub fn initialize(&mut self) {
        self.fast = 0.0;
        self.slow = 0.0;
        self.calf = 0.0;
        self.cals = 0.0;
    }
}

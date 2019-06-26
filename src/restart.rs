use crate::propagator::AssignStack;
use crate::state::{Stat, State};
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

impl RestartIF for State {
    fn block_restart(&mut self, asgs: &AssignStack, ncnfl: usize) -> bool {
        let nas = asgs.len();
        // let _count = self.stats[Stat::Conflict];
        // let _ave = self.sum_asg / count as f64 * self.num_vars as f64;
        if 100 < ncnfl
            && !self.use_luby_restart
            && self.restart_step <= self.after_restart
            && self.restart_blk * self.ema_asg.get() < nas as f64
        {
            self.after_restart = 0;
            self.stats[Stat::BlockRestart] += 1;
            return true;
        }
        false
    }
    fn force_restart(&mut self, ncnfl: &mut f64) -> bool {
        let count = self.stats[Stat::Conflict];
        // if count <= RESET_EMA {
        //     if count == RESET_EMA {
        //         self.ema_asg.reset();
        //         self.ema_lbd.reset();
        //     }
        //     return false;
        // }
        let ave = self.stats[Stat::SumLBD] as f64 / count as f64;
        if (self.use_luby_restart && self.luby_restart_num_conflict <= *ncnfl)
            || (!self.use_luby_restart
                && self.restart_step <= self.after_restart
                && ave < self.ema_lbd.get() * self.restart_thr)
            || self.force_restart_by_stagnation
        {
            self.stats[Stat::Restart] += 1;
            self.after_restart = 0;
            if self.use_luby_restart {
                *ncnfl = 0.0;
                self.luby_current_restarts += 1;
                self.luby_restart_num_conflict =
                    luby(self.luby_restart_inc, self.luby_current_restarts)
                        * self.luby_restart_factor;
            }
            if self.force_restart_by_stagnation {
                self.force_restart_by_stagnation = false;
            }
            return true;
        }
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

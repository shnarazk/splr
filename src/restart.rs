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
    fn restart(&mut self, nasg: usize, dl: usize, cnfl_ratio: &mut f64) -> bool {
        // Firstly do all tasks for Luby
        if self.use_luby_restart {
            if self.luby_restart_num_conflict <= *cnfl_ratio {
                self.stats[Stat::Restart] += 1;
                *cnfl_ratio = 0.0;
                self.luby_current_restarts += 1;
                self.luby_restart_num_conflict =
                    luby(self.luby_restart_inc, self.luby_current_restarts)
                    * self.luby_restart_factor;
                return true;
            }
            return false;
        }
        let ncnfl = self.stats[Stat::Conflict];
        // NOTE: due to continuous conflicts, 'ncnfl == next_restart' might be skipped.
        if ncnfl < self.next_restart {
            return false;
        }
        let ave_lbd = self.stats[Stat::SumLBD] as f64 / ncnfl as f64;
        let _force_cond = ave_lbd < self.ema_lbd.get() * self.restart_thr;
        let _force_cond_proven_bad = self.va_dist_ema.rate() < 1.0;
        let force_cond0 = self.c_lvl.get() < 0.7 * self.c_lvl.get_fast();
        let _block_cond = self.ema_asg.get() < 0.85 * nasg as f64; // self.restart_blk
        let block_cond0 = self.restart_blk < self.va_dist_ema.rate();

        // FORCING RESTART PATH
        if force_cond0 && !block_cond0 {
            self.stats[Stat::Restart] += 1;
            self.ema_restart_len.update(self.after_restart as f64);
            self.after_restart = 0;
            self.next_restart = ncnfl + 2 * self.restart_step;
            self.ema_conflict_clash.update(0.0);
            return true;
        }
        // fine grain BLOCKING RESTART PATH
        if !force_cond0 && block_cond0
        {
            self.next_restart = ncnfl + self.restart_step;
            if dl < self.b_lvl.get() as usize {
                self.next_restart += self.restart_step;
            }
            self.stats[Stat::BlockRestart] += 1;
            // self.ema_deep_search.update(self.after_restart as f64);
            return false;
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
        self.slow = self.fast;
        self.cals = self.calf;
    }
}

impl Ema2 {
    pub fn rate(&self) -> f64 {
        self.fast / self.slow * (self.cals / self.calf)
    }
    pub fn with_fast(mut self, f: usize) -> Ema2 {
        self.fe = 1.0 / (f as f64);
        self
    }
    fn get_fast(&self) -> f64 {
        self.fast / self.calf
    }
}

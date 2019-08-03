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
    // Fold-based restart engine
    fn restart(&mut self, asgs: &mut AssignStack, vdb: &mut VarDB) -> bool {
        if self.use_luby_restart {
            if self.luby_restart_num_conflict <= self.luby_restart_cnfl_cnt {
                self.stats[Stat::LubyRestart] += 1;
                self.after_restart = 0;
                self.luby_restart_cnfl_cnt = 0.0;
                self.luby_current_restarts += 1;
                self.luby_restart_num_conflict =
                    luby(self.luby_restart_inc, self.luby_current_restarts)
                        * self.luby_restart_factor;
                return true;
            }
            return false;
        }
        self.after_restart += 1;

        /*
        if 0 < self.restart_block_step {
            self.restart_block_step -= 1;
            self.b_lvl.update(bl as f64);
            self.partial_restart_ratio.update(0.0);
            return false;
        }
         */

        let ncnfl = self.stats[Stat::Conflict];
        let bl = asgs.level();
        let bj = (bl / 2).max(self.root_level);
        let _nvar = self.num_vars - self.num_solved_vars - self.num_eliminated_vars;
        let folding_ratio = self.ema_folds_ratio.get();
        let folding_trend = self.ema_folds_ratio.trend();
        let restart_ratio = self.partial_restart_ratio.get();
        let scale = 1 + self.slack_duration; // 1 + self.stats[Stat::Restart];

        let full_covered_condition: bool =
            folding_ratio < 0.1 / (scale as f64).sqrt()
            // && folding_trend < 0.025 / (scale as f64).sqrt()
            // && folding_trend < 0.25
            // && 1_000 * scale < self.after_restart
            && 1_000 < self.after_restart
            ;

        let glucose_restart_condition: bool =
        {
            let average_lbd = self.stats[Stat::SumLBD] as f64 / ncnfl as f64;
            // let a = self.slack_duration as f64;
            // (average_lbd + a) / (1.0 + a) < self.ema_lbd.get() * self.restart_thr
            average_lbd < self.ema_lbd.get() * self.restart_thr
        };

        let _glucose_blocking_condition: bool =
            self.restart_blk * self.ema_asg.get() < asgs.len() as f64
            ;

        let global_restart_condition: bool =
            full_covered_condition
            && 0 < self.num_partial_restart
            ;

        let partial_restart_condition: bool =
            glucose_restart_condition
            && bj < bl
            ;

        if global_restart_condition
            && 0 < self.num_partial_restart
        { // stop a exhaustive search and restart
            asgs.cancel_until(vdb, 0);
            self.b_lvl.update(0.0);
            self.partial_restart_ratio.update(1.0);
            vdb.reset_folding_points();
            vdb.activity_decay = self.config.var_activity_decay;
            // vdb.activity_decay
            //     += (self.num_folding_vars as f64 / self.num_folding_vars_last as f64)
            //     .sqrt()
            //     .min(0.999);
            // vdb.activity_decay *= 0.5;
            // if 1 < self.slack_duration {
            //     let k: f64 = (self.slack_duration as f64).log(10.0);
            //     vdb.activity_decay = (vdb.activity_decay + k) / (k + 1.0);
            // }
            // if vdb.activity_decay < 0.96 {
            //     vdb.activity_decay *= 1.001; // make sure to keep a large range
            // }
            self.num_folding_vars_last = self.num_folding_vars;
            self.num_folding_vars = 0;
            self.num_partial_restart = 0;
            self.num_partial_restart_try = 0;
            self.ema_folds_ratio.reinitialize1();
            self.after_restart = 0;
            self.stats[Stat::Restart] += 1;
        } else if partial_restart_condition
            && restart_ratio < folding_ratio
            && self.num_partial_restart_try <= self.num_folding_vars
        {
            asgs.cancel_until(vdb, bj);
            self.b_lvl.update(bj as f64);
            self.num_partial_restart += 1;
            self.num_partial_restart_try += 1;
            self.stats[Stat::PartialRestart] += 1;
            if false {
                // reset some counters on folding
                vdb.reset_folding_points();
                self.num_folding_vars = 0;
                self.ema_folds_ratio.reinitialize1();
            }
            // end of the reset block
            self.partial_restart_ratio.update(1.0); // with a bonus
            // increment only based on sucessful partial restarts
            vdb.activity_decay = {
                let n: f64 = self.num_partial_restart as f64 / 100.0;
                let s: f64 = self.config.var_activity_decay;
                (n + s) / (n + 1.0)
            };
        } else {
            if partial_restart_condition && folding_trend < 0.5 {
                self.num_partial_restart_try += 1;
            }
            self.b_lvl.update(bl as f64);
            self.partial_restart_ratio.update(0.0);
            return false;
        }
        true
    }

    /// return true to forcing restart. Otherwise false.
    fn check_restart(&mut self, asgs: &AssignStack, _vdb: &mut VarDB) -> bool {
        let _ncnfl = self.stats[Stat::Conflict];
        let _nas = asgs.len();
        // polar parameters
        let _epsilon = 0.05;
        // first, handle Luby path
        if self.use_luby_restart {
            if self.luby_restart_num_conflict <= self.luby_restart_cnfl_cnt {
                self.stats[Stat::LubyRestart] += 1;
                self.after_restart = 0;
                self.luby_restart_cnfl_cnt = 0.0;
                self.luby_current_restarts += 1;
                self.luby_restart_num_conflict =
                    luby(self.luby_restart_inc, self.luby_current_restarts)
                        * self.luby_restart_factor;
                return true;
            }
            if 0.8 < self.ema_folds_ratio.trend() && 4.0 * self.ema_lbd.get() < self.c_lvl.get() {
                self.use_luby_restart = false;
            }
            return false;
        }
        if self.after_restart < self.restart_step {
            return false;
        }
        /*
                if (self.num_vars - self.num_eliminated_vars < 2 * self.num_polar_vars
                    || self.ema_folds_inc.get() < 0.0001)
                    && self.ema_folds_inc.ratio() < 0.5
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
    /// return true to block restart.
    fn block_restart(&mut self, asgs: &AssignStack) -> bool {
        if self.use_luby_restart || 0 < self.restart_block_step {
            return false;
        }
        if self.restart_blk * self.ema_asg.get() < asgs.len() as f64 {
            self.restart_block_step = self.restart_step;
            self.after_restart = 0;
            self.stats[Stat::BlockRestart] += 1;
            return false;
        }
        false
    }
    fn restart_update_lbd(&mut self, lbd: usize) {
        self.ema_lbd.update(lbd as f64);
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
    pub fn trend(&self) -> f64 {
        self.fast / self.slow * (self.cals / self.calf)
    }
    pub fn with_fast(mut self, f: u64) -> Self {
        self.fe = 1.0 / (f as f64);
        self
    }
    pub fn initialize1(mut self) -> Self {
        self.reinitialize1();
        self
    }
    pub fn reinitialize1(&mut self) {
        self.fast = 1.0;
        self.slow = 1.0;
        self.calf = 1.0;
        self.cals = 1.0;
    }
}

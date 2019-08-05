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
        let ncnfl = self.stats[Stat::Conflict];
        let _scale = 1 + self.slack_duration; // 1 + self.stats[Stat::Restart];
        let scale: f64 = vdb.num_current_folding_vars as f64
            / vdb.num_folding_vars as f64;
        // (self.num_vars - self.num_eliminated_vars) as f64;
        let bl = asgs.level();
        let _bj = (bl / 2).max(self.root_level);
        let bj = (((1.0 - scale) * bl as f64) as usize).max(self.root_level);
        let apc_ratio = self.ema_asg_progress.get();
        let apc_fast =  self.ema_asg_progress.get_fast();
        let _apc_trend =  self.ema_asg_progress.trend();
        let folding_ratio = self.ema_folds_ratio.get();
        let folding_fast = self.ema_folds_ratio.get_fast();
        let folding_trend = self.ema_folds_ratio.trend();
        let restart_ratio = self.partial_restart_ratio.get();


        let full_covered_condition: bool =
            vdb.num_folding_vars == vdb.num_current_folding_vars
                // folding_ratio < 0.02 / (scale as f64).sqrt()
            && 0.2 < folding_ratio
            && 1.0 < folding_trend
                // && folding_trend < 0.1 // (scale as f64).sqrt()
                // && folding_trend < 0.025 / (scale as f64).sqrt()
                // && folding_trend < 0.25
                // && 1_000 * scale < self.after_restart
            && 1_000 < self.after_restart
            ;

        let glucose_restart_condition: bool =
        {
            let average_lbd = self.stats[Stat::SumLBD] as f64 / ncnfl as f64;
            self.restart_thr * average_lbd < self.ema_lbd.get()
        };

        let glucose_blocking_condition: bool =
        {
            // let cover: f64 = vdb.num_current_folding_vars as f64 / self.num_vars as f64;
            // let cover: f64 = vdb.num_current_folding_vars as f64 / vdb.num_folding_vars as f64;
            // self.restart_blk * self.ema_asg.get() < asgs.len() as f64
            // self.restart_blk < self.ema_asg.trend()
            // self.restart_blk * cover < self.ema_asg.trend()
            self.restart_blk * (self.stats[Stat::SumASG] as f64) < asgs.len() as f64
        };

        let assignment_improve_condition: bool =
            0.0 <= apc_ratio
            || 0.0 <= apc_fast
            ;
        
        let assignment_stagnated_condition: bool =
        {
            let thrd = vdb.num_folding_vars as f64 / 1000.0;
            apc_ratio.abs() < thrd
                && apc_fast.abs() < thrd / 2.0
        };
        
        let restartable_condition: bool =
        {
            let _cover: f64 = vdb.num_current_folding_vars as f64
                / vdb.num_folding_vars as f64;
            folding_ratio < 0.4
                && folding_fast < 0.2
        };

        let most_covered_condition: bool =
        {
            let _cover: f64 = vdb.num_current_folding_vars as f64
                / vdb.num_folding_vars as f64;
            folding_ratio < 0.2
                && folding_fast < 0.1
        };

        let partial_restart_condition: bool = true
            // !glucose_blocking_condition
            // && !assignment_improve_condition
            && glucose_restart_condition
            && bj < bl
            && restartable_condition
            // && self.root_level < bj
            ;

        let _global_restart_condition: bool =
            !assignment_improve_condition
            && full_covered_condition
            && 0 < self.num_partial_restart
            ;

        let global_restart_condition: bool =
            !glucose_blocking_condition
            && ((glucose_restart_condition
                 && bj < bl
                 && most_covered_condition
                 && self.root_level == bj)
                || assignment_stagnated_condition)
            // && most_covered_condition
            ;

        if global_restart_condition
            // && most_covered_condition
            && 0 < self.num_partial_restart
        { // stop a exhaustive search and restart
            asgs.cancel_until(vdb, 0);
            asgs.check_progress();
            self.b_lvl.update(0.0);
            self.partial_restart_ratio.update(1.0);
            vdb.reset_folding_points();
            vdb.activity_decay = self.config.var_activity_decay;
            self.num_partial_restart = 0;
            self.num_partial_restart_try = 0;
            self.ema_folds_ratio.reinitialize1();
            self.after_restart = 0;
            self.stats[Stat::Restart] += 1;
            self.stats[Stat::SumASG] = 0;
        } else if partial_restart_condition
            && most_covered_condition
            && restart_ratio < scale * folding_ratio
            && self.num_partial_restart_try <= vdb.num_current_folding_vars
        {
            asgs.cancel_until(vdb, bj);
            asgs.check_progress();
            self.b_lvl.update(bj as f64);
            self.num_partial_restart += 1;
            self.num_partial_restart_try += 1;
            self.stats[Stat::PartialRestart] += 1;
            if false {
                // reset some counters on folding
                vdb.reset_folding_points();
                self.ema_folds_ratio.reinitialize1();
            }
            self.partial_restart_ratio.update(1.0); // with a bonus
            // increment only based on sucessful partial restarts
            vdb.activity_decay = {
                let n: f64 = self.num_partial_restart as f64 / 100.0;
                let s: f64 = self.config.var_activity_decay;
                (n + s) / (n + 1.0)
            };
        } else {
            if partial_restart_condition {
                self.num_partial_restart_try += 1;
            }
            self.b_lvl.update(bl as f64);
            self.partial_restart_ratio.update(0.0);
            return false;
        }
        true
    }

    fn restart_update_lbd(&mut self, lbd: usize) {
        self.ema_lbd.update(lbd as f64);
        self.stats[Stat::SumLBD] += lbd;
    }
    fn restart_update_asg(&mut self, n: usize) {
        self.ema_asg.update(n as f64);
        self.stats[Stat::SumASG] = self.stats[Stat::SumASG].max(n);
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
    pub fn with_fast(mut self, f: usize) -> Self {
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
    }
}

use crate::propagator::AssignStack;
use crate::state::{Stat, State};
use crate::traits::*;
use crate::types::Flag;
use crate::var::VarDB;

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

impl RestartIF for State {
    // stagnation-triggered restart engine
    fn restart(&mut self, asgs: &mut AssignStack, vdb: &mut VarDB) -> bool {
        if self.use_luby_restart {
            if self.luby_restart_num_conflict <= self.luby_restart_cnfl_cnt {
                self.stats[Stat::Restart] += 1;
                self.stats[Stat::RestartByLuby] += 1;
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
        let mut level0_restart = false;
        let mut level1_restart = false;
        let mut level2_restart = false;
        let sup = |long, rate, thrd| rate < thrd && long < thrd && rate < long;

        // level 0
        if vdb.asv.check(sup) {
            // level0_restart = true;
            // self.stats[Stat::RestartByAsg] += 1;
        }

        // level 1
        vdb.acv.check(sup);
        vdb.fup.check(|long, _rate, _thrd| long < 0.01);
        level1_restart = vdb.acv.is_closed & vdb.fup.is_closed;

        if level1_restart {
            self.stats[Stat::RestartByAsg] += 1;
            self.stats[Stat::RestartByFUP] += 1;
        }

        // level 2
        if vdb.sua.check(sup) {
            // level2_restart = true;
            // self.stats[Stat::RestartBySuA] += 1;
        }
        if vdb.suf.check(sup) {
            // level2_restart = true;
            // self.stats[Stat::RestartBySuF] += 1;
        }

        if level0_restart || level1_restart || level2_restart {
            asgs.cancel_until(vdb, 0);
            asgs.check_progress();
            self.b_lvl.update(0.0);
            self.restart_ratio.update(1.0);
            // level 2 are never cleared.
            if level0_restart || level1_restart || level2_restart {
                // No need to asv.remove. It has a pseudo flag.
                vdb.asv.reset();
            }
            if level1_restart || level2_restart {
                let VarDB {
                    ref mut vars,
                    ref mut acv,
                    ref mut fup,
                    ..
                } = vdb;
                for v in &mut vars[1..] {
                    if !v.is(Flag::ELIMINATED) {
                        acv.remove(v);
                        fup.remove(v);
                    }
                }
                acv.reset();
                fup.reset();
            }
            self.after_restart = 0;
            self.stats[Stat::Restart] += 1;
            {
                let ra = self.stats[Stat::RestartByAsg];
                let rf = self.stats[Stat::RestartByFUP];
                if 0 < ra && 0 < rf {
                    let s = self.config.var_activity_decay;
                    let m = self.config.var_activity_d_max;
                    let k = ra.max(rf) as f64 / (ra + rf) as f64;
                    vdb.activity_decay = k * m + (1.0 - k) * s;
                }
            }
            true
        } else {
            let bl = asgs.level();
            self.b_lvl.update(bl as f64);
            self.restart_ratio.update(0.0);
            false
        }
    }

    fn restart_update_lbd(&mut self, lbd: usize) {
        self.sum_lbd += lbd;
        self.ema_lbd.update(lbd as f64);
    }
    fn restart_update_asg(&mut self, n: usize) {
        self.ema_asg.update(n as f64);
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

use crate::propagator::AssignStack;
use crate::state::{Stat, State};
use crate::traits::*;
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
        let mut level1_restart = false;
        let mut level2_restart = false;

        //////////////// level 1
        //////// asv
        {
            let asv_long = self.ema_asv_inc.get();
            let asv_rate = self.ema_asv_inc.get_fast();
            let thrd = vdb.asv_threshold;
            let v = asv_rate < thrd && asv_long < thrd && asv_rate < asv_long;
            if !vdb.asv_is_closed {
                self.ema_asv_inc.update(vdb.asv_inc as f64);
                vdb.asv_inc = 0.0;
                if v {
                    vdb.asv_is_closed = true;
                    level1_restart = true;
                    self.stats[Stat::RestartByAsg] += 1;
                }
            }
        };
        //////// acv
        {
            let acv_long = self.ema_acv_inc.get();
            let acv_rate = self.ema_acv_inc.get_fast();
            let thrd = vdb.acv_stagnation_threshold;
            let v = acv_rate < thrd && acv_rate < acv_long && acv_long < thrd;
            if !vdb.acv_is_closed {
                self.ema_acv_inc.update(vdb.acv_inc as f64);
                vdb.acv_inc = 0.0;
                if v {
                    vdb.acv_is_closed = true;
                    // level1_restart = true;
                    // self.stats[Stat::RestartByAsg] += 1;
                }
            }
        }

        //////// fup
        {
            let fup_long = self.ema_fup_inc.get();
            let fup_rate = self.ema_fup_inc.get_fast();
            let thrd = vdb.fup_stagnation_threshold;
            let v = fup_rate < thrd && fup_rate < fup_long && fup_long < thrd;
            if !vdb.fup_is_closed {
                self.ema_fup_inc.update(vdb.fup_inc as f64);
                vdb.fup_inc = 0.0;
                if v {
                    vdb.fup_is_closed = true;
                    // level1_restart = true;
                    // self.stats[Stat::RestartByFUP] += 1;
                }
            }
        };

        //////////////// level 2
        //////// sua
        {
            let sua_long = self.ema_sua_inc.get();
            let sua_rate = self.ema_sua_inc.get_fast();
            let thrd = vdb.sua_stagnation_threshold;
            let v = sua_rate < thrd && sua_rate < sua_long && sua_long < thrd;
            if !vdb.sua_is_closed {
                self.ema_sua_inc.update(vdb.sua_inc as f64);
                vdb.sua_inc = 0.0;
                if v {
                    vdb.sua_is_closed = true;
                    // level2_restart = true;
                    // self.stats[Stat::RestartBySUA] += 1;
                }
            }
        };

        //////// suf
        {
            let suf_long = self.ema_suf_inc.get();
            let suf_rate = self.ema_suf_inc.get_fast();
            let thrd = vdb.suf_stagnation_threshold;
            let v = suf_rate < thrd && suf_rate < suf_long && suf_long < thrd;
            if !vdb.suf_is_closed {
                self.ema_suf_inc.update(vdb.suf_inc as f64);
                vdb.suf_inc = 0.0;
                if v {
                    vdb.suf_is_closed = true;
                    level2_restart = true;
                    self.stats[Stat::RestartByFUP] += 1; // BySUF
                }
            }
        };

        if level1_restart || level2_restart {
            asgs.cancel_until(vdb, 0);
            asgs.check_progress();
            self.b_lvl.update(0.0);
            self.restart_ratio.update(1.0);
            if true {
                vdb.reset_asv();
                self.ema_asv_inc.reinitialize1();
            }
            if level1_restart || level2_restart {
                vdb.reset_acv();
                self.ema_acv_inc.reinitialize1();
                vdb.reset_fup();
                self.ema_fup_inc.reinitialize1();
            }
            if level2_restart {
                vdb.reset_sua();
                self.ema_sua_inc.reinitialize1();
                vdb.reset_suf();
                self.ema_suf_inc.reinitialize1();
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

use crate::propagator::AssignStack;
use crate::state::{Stat, State};
use crate::traits::*;
use crate::types::Flag;
use crate::var::{VarDB, VarSet};

const CLOSE_THRD: f64 = 0.5; // 0.72;

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

/// Glucose original (or Lingering-style) forcing restart condition
/// ### Implementing the original algorithm
///
/// ```ignore
///    rst = RestartLBD::new(1.4);
///    rst.add(learnt.lbd());
///    if rst.update(|ema, ave| rst.threshold * ave < ema.get()) {
///        restarting...
///    }
/// ```
///
/// ### Implementing an EMA-pair-based variant
///
/// ```ignore
///    rst = RestartLBD2::new(1.4);
///    rst.add(learnt.lbd());
///    if rst.update(|ema, _| rst.threshold * ema.get() < ema.get_fast()) {
///        restarting...
///    }
/// ```
#[derive(Debug)]
pub struct RestartLBD {
    pub sum: f64,
    pub num: usize,
    pub threshold: f64,
    pub ema: Ema,
    lbd: Option<usize>,
    result: bool,
    timer: usize,
}

impl ProgressEvaluatorIF<'_> for RestartLBD {
    type Memory = Ema;
    type Item = usize;
    fn add(&mut self, item: Self::Item) -> &mut RestartLBD {
        // assert_eq!(self.lbd, None);
        self.sum += item as f64;
        self.num += 1;
        self.lbd = Some(item);
        self
    }
    fn update<F>(&mut self, f: F) -> bool
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        if let Some(lbd) = self.lbd {
            self.ema.update(lbd as f64);
            self.lbd = None;
            if 0 < self.timer {
                self.timer -= 1;
                false
            } else {
                self.result = f(&self.ema, self.sum / self.num as f64);
                if self.result {
                    self.timer = 10;
                }
                self.result
            }
        } else {
            panic!("RestartLBD: you tried to update without add");
        }
    }
    fn is_active(&self) -> bool {
        0 < self.timer && self.result
    }
    fn check<F>(&mut self, f: F) -> bool
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        assert!(self.lbd.is_none());
        f(&self.ema, self.sum / self.num as f64)
    }
}

impl RestartLBD {
    pub fn new(threshold: f64) -> Self {
        RestartLBD {
            sum: 0.0,
            num: 0,
            threshold,
            ema: Ema::new(75),
            lbd: None,
            result: false,
            timer: 0,
        }
    }
}

/// Glucose original (or Lingering-style) restart blocking condition
/// ### Implementing the original algorithm
///
/// ```ignore
///    blk = RestartASG::new(1.0 / 0.8);
///    blk.add(solver.num_assigns);
///    if blk.update(|ema, ave| blk.threshold * ave < ema.get()) {
///        blocking...
///    }
/// ```
/// ### Implementing an EMA-pair-based variant
///
/// ```ignore
///    blk = RestartASG2::new(1.0 / 0.8);
///    blk.add(solver.num_assigns);
///    if blk.update(|ema, _| blk.threshold * ema.get() < ema.get_fast()) {
///        blocking...
///    }
/// ```
#[derive(Debug)]
pub struct RestartASG {
    pub sum: usize,
    pub num: usize,
    pub threshold: f64,
    pub ema: Ema,
    asg: Option<usize>,
    result: bool,
    timer: usize,
}

impl ProgressEvaluatorIF<'_> for RestartASG {
    type Memory = Ema;
    type Item = usize;
    fn add(&mut self, item: Self::Item) -> &mut Self {
        assert!(self.asg.is_none());
        self.sum += item;
        self.num += 1;
        self.asg = Some(self.asg.map_or(item, |v| v + item));
        self
    }
    fn update<F>(&mut self, f: F) -> bool
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        if let Some(a) = self.asg {
            self.ema.update(a as f64);
            self.asg = None;
            if 0 < self.timer {
                self.timer -= 1;
                return true;
            } else {
                self.result = f(&self.ema, self.sum as f64 / self.num as f64);
                if self.result {
                    self.timer = 25;
                }
                self.result
            }
        } else {
            panic!("RestartASG: you tried to update without add");
        }
    }
    fn is_active(&self) -> bool {
        0 < self.timer && self.result
    }
    fn check<F>(&mut self, f: F) -> bool
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        assert!(self.asg.is_none());
        f(&self.ema, self.sum as f64 / self.num as f64)
    }
}

impl RestartASG {
    pub fn new(threshold: f64) -> Self {
        RestartASG {
            sum: 0,
            num: 0,
            threshold,
            ema: Ema::new(200),
            asg: None,
            result: false,
            timer: 10,
        }
    }
}

#[derive(Debug)]
pub struct RestartLuby {
    pub in_use: bool,
    pub num_conflict: f64,
    pub inc: f64,
    pub current_restart: usize,
    pub factor: f64,
    pub cnfl_cnt: f64,
    result: bool,
}

impl ProgressEvaluatorIF<'_> for RestartLuby {
    type Memory = usize;
    type Item = ();
    fn add(&mut self, _item: Self::Item) -> &mut Self {
        if self.in_use {
            self.cnfl_cnt += 1.0;
        }
        self
    }
    fn update<F>(&mut self, _f: F) -> bool
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        if self.in_use && self.num_conflict <= self.cnfl_cnt {
            self.cnfl_cnt = 0.0;
            self.current_restart += 1;
            self.num_conflict = luby(self.inc, self.current_restart) * self.factor;
            self.result = true;
        } else {
            self.result = false;
        }
        self.result
    }
    fn is_active(&self) -> bool {
        self.result
    }
    fn check<F>(&mut self, _f: F) -> bool
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        panic!("RestartLuby doesn't implement check.");
    }
}

impl Default for RestartLuby {
    fn default() -> Self {
        RestartLuby {
            in_use: false,
            num_conflict: 0.0,
            inc: 2.0,
            current_restart: 0,
            factor: 100.0,
            cnfl_cnt: 0.0,
            result: false,
        }
    }
}

impl RestartLuby {
    pub fn new(inc: f64, factor: f64) -> Self {
        RestartLuby {
            in_use: false,
            num_conflict: 0.0,
            inc,
            current_restart: 0,
            factor,
            cnfl_cnt: 0.0,
            result: false,
        }
    }
    pub fn initialize(&mut self, in_use: bool) -> &mut Self {
        self.in_use = in_use;
        if self.in_use {
            self.num_conflict = luby(self.inc, self.current_restart) * self.factor;
        }
        self
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
        let sup = |e2: &Ema2, thrd| {
            let long = e2.get();
            let rate = e2.get_fast();
            rate < thrd && long < thrd && rate < long
        };
        self.rst.asg.update(|ema, ave| 1.05 * ave < ema.get()); // to stop
        self.rst.lbd.update(|ema, ave| 2.0 * ave < ema.get());  // to force
        self.rst.asv.update(sup);
        // self.rst.acv.update(sup);
        self.rst.fup.update(|e2, _| e2.get_fast() < 0.25);
        // self.rst.sua.update(sup);
        // self.rst.suf.update(sup);

        let level0_restart = if !self.rst.asg.is_active() && self.rst.lbd.is_active()
        // && !self.rst.asv.is_active()
        {
            self.stats[Stat::RestartByAsg] += 1;
            true
        }
        /* else if self.rst.asg.should_restart() {
          // This is ant-blocking condition.
          // self.stats[Stat::BlockingByAsg] += 1;
          // false
        } */
        else {
            false
        };

        let level1_restart =
            /* if self.rst.fup.is_active() {
                level1_restart = true;
                self.stats[Stat::RestartByAsg] += 1;
                self.stats[Stat::RestartByFUP] += 1;
            } */
            false;

        let level2_restart =
            /*
            if self.rst.sua.is_active() {
               level2_restart = true;
               self.stats[Stat::RestartBySuA] += 1;
           } */
            false;

        if level0_restart || level1_restart {
            asgs.cancel_until(vdb, 0);
            asgs.check_progress();
            self.restart_ratio.update(1.0);
            // No need to call remove nor reset for asv. It's memoryless. 
            if level1_restart || level2_restart {
                for v in &mut vdb[1..] {
                    if !v.is(Flag::ELIMINATED) {
                        self.rst.acv.remove(v);
                        self.rst.fup.remove(v);
                    }
                }
                self.rst.acv.reset();
                self.rst.fup.reset();
            }
            // level 2 are never cleared.
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
            self.restart_ratio.update(0.0);
            false
        }
    }
    fn restart_update_luby(&mut self) {
        if self.use_luby_restart {
            self.luby_restart_num_conflict =
                luby(self.luby_restart_inc, self.luby_current_restarts) * self.luby_restart_factor;
        }
    }
}

/// Exponential Moving Average w/ a calibrator
/// ### About levels
///
/// - Level 0 is a memory cleared at each restart
/// - Level 1 is a memory held during restarts but clear after mega-restart
/// - Level 2 is a memory not to reset by restarts
/// *Note: all levels clear after finding a unit learnt (simplification).*
#[derive(Debug)]
pub struct ProgressEvaluatorPack {
    pub lbd: RestartLBD,
    pub asg: RestartASG,
    pub asv: VarSet,
    pub acv: VarSet,
    pub sua: VarSet,
    pub fup: VarSet,
    pub suf: VarSet,
}

impl ProgressEvaluatorPack {
    pub fn new(n: usize) -> ProgressEvaluatorPack {
        let scale: f64 = (n as f64).log(2f64);
        ProgressEvaluatorPack {
            lbd: RestartLBD::new(0.1),
            asg: RestartASG::new(0.1),
            asv: VarSet::new(None, CLOSE_THRD * scale),
            acv: VarSet::new(Some(Flag::ACV), CLOSE_THRD * scale),
            sua: VarSet::new(Some(Flag::SUA), CLOSE_THRD * scale),
            fup: VarSet::new(Some(Flag::FUP), 0.05),
            suf: VarSet::new(Some(Flag::SUF), CLOSE_THRD),
        }
    }
}

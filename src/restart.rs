use crate::config::{EMA_FAST, EMA_SLOW, RESTART_INTV, RESTART_QNTM, RESTART_THRD};
use crate::traits::*;
use crate::types::Flag;
use crate::var::{Var, VarDB};

const RESTART_THRESHOLD: f64 = 1.6;

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
    fn initialize(mut self, init: f64) -> Self {
        self.val = init;
        self
    }
    fn reinitialize(&mut self, init: f64) -> &mut Self {
        self.val = init;
        self
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
    fn initialize(mut self, init: f64) -> Self {
        self.fast = init;
        self.slow = init;
        self
    }
    fn reinitialize(&mut self, init: f64) -> &mut Self {
        // self.fast = self.slow;
        // self.fast = init * self.calf;
        // self.slow = init * self.cals;
        self.fast = init; // self.fe * x + (1.0 - self.fe) * self.fast;
        self.slow = init; // self.se * x + (1.0 - self.se) * self.slow;
        self.calf = 0.0;
        self.cals = 0.0;
        self
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
}

/// A Luby + First-UIP driven Restart Engine
#[derive(Debug)]
pub struct RestartExecutor {
    pub interval_ema: Ema,
    pub ratio: Ema,
    pub threshold: (f64, f64),
    pub use_luby: bool,
    pub asg: RestartASG,
    pub fup: VarSet,
    pub lbd: RestartLBD,
    pub luby: RestartLuby,
    after_restart: usize,
    interval: usize,
    quantumize: usize,
    trend_dir: (bool, usize),
    trend_duration: usize,
    qtrend_band: (usize, usize),
}

impl Default for RestartExecutor {
    fn default() -> Self {
        RestartExecutor {
            ratio: Ema::new(EMA_SLOW),
            interval: RESTART_INTV,
            interval_ema: Ema::new(EMA_SLOW),
            quantumize: RESTART_QNTM,
            threshold: RESTART_THRD, // (fup.trend, decay factor),
            use_luby: false,
            asg: RestartASG::new(RESTART_THRESHOLD),
            fup: VarSet::new(Flag::FUP),
            lbd: RestartLBD::new(RESTART_THRESHOLD),
            luby: RestartLuby::new(2.0, 100.0),
            after_restart: 1,
            trend_dir: (true, 0),
            trend_duration: 0,
            qtrend_band: (0, 1000),
        }
    }
}
impl RestartExecutor {
    pub fn new(interval: usize, quantumize: usize) -> RestartExecutor {
        let mut re = RestartExecutor::default();
        re.interval = interval;
        re.quantumize = quantumize;
        re
    }
}

impl RestartIF for RestartExecutor {
    fn restart(&mut self, vdb: &mut VarDB) -> bool {
        if self.use_luby {
            self.luby.update(true);
            return self.luby.is_active();
        }
        let RestartExecutor {
            after_restart,
            fup,
            interval,
            quantumize,
            threshold,
            trend_dir,
            qtrend_band,
            ..
        } = self;
        let (band_min, band_max) = qtrend_band;
        let mut restart_point = false;
        let r_trend = fup.trend();
        let q_trend = (r_trend * *quantumize as f64) as usize;
        *after_restart += 1;
        // * trend_dir.0: fup's trend is increasing
        // * trend_dir.1: its duration
        if trend_dir.0 {
            if *band_max < q_trend {
                trend_dir.1 += 1;
                *band_max = q_trend;
            } else if *band_max == q_trend {
                if 0 < trend_dir.1 {
                    trend_dir.1 += 1;
                }
            } else {
                if *interval < trend_dir.1
                    && 4 <= *band_max - *band_min
                    && 3 <= *band_max - q_trend
                {
                    restart_point = true;
                    *trend_dir = (false, 0);
                    *band_min = *band_max;
                } else if q_trend < *band_min {
                    *trend_dir = (false, 0);
                    *band_min = *band_max;
                } else {
                    trend_dir.1 += 1;
                }
            }
        } else {
            if q_trend < *band_min {
                trend_dir.1 += 1;
                *band_min = q_trend;
            } else if q_trend == *band_min {
                if 0 < trend_dir.1 {
                    trend_dir.1 += 1;
                }
            } else {
                if *interval <= trend_dir.1
                    && 4 <= *band_max - *band_min
                    && 3 <= q_trend - *band_min
                {
                    // restart_point = true;
                    *trend_dir = (true, 0);
                    *band_max = *band_min;
                } else if *band_max < q_trend {
                    *trend_dir = (true, 0);
                    *band_max = *band_min;
                } else {
                    trend_dir.1 += 1;
                }
            }
        }
        if *interval <= trend_dir.1 && r_trend < threshold.0 {
            trend_dir.1 = 0;
            *qtrend_band = (*quantumize, 0);
            threshold.0 *= threshold.1;
            self.reset_fup(vdb);
            restart_point = true;
        }
        if restart_point {
            self.interval_ema.update(self.after_restart as f64);
            self.after_restart = 0;
            return true;
        }
        false
    }
    fn reset_fup(&mut self, vdb: &mut VarDB) {
        for v in &mut vdb.vars[1..] {
            self.fup.remove(v);
        }
        self.fup.reset();
    }
}

/// Glucose-style forcing restart condition w/o restart_steps
/// ### Implementing the original algorithm
///
/// ```ignore
///    rst = RestartLBD::new(1.4);
///    rst.add(learnt.lbd()).commit();
///    if rst.eval(|ema, ave| rst.threshold * ave < ema.get()) {
///        restarting...
///    }
/// ```
///
#[derive(Debug)]
pub struct RestartLBD {
    pub sum: f64,
    pub num: usize,
    pub threshold: f64,
    pub ema: Ema,
    lbd: Option<usize>,
    result: bool,
}

impl ProgressEvaluatorIF<'_> for RestartLBD {
    type Memory = Ema;
    type Item = usize;
    fn update(&mut self, item: Self::Item) {
        self.sum += item as f64;
        self.num += 1;
        self.ema.update(item as f64)
    }
    fn update_with<F>(&mut self, f: F) -> &mut Self
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        assert!(self.lbd.is_none());
        self.result = f(&self.ema, self.sum / self.num as f64);
        self
    }
    fn is_active(&self) -> bool {
        self.result
    }
    fn eval<F, R>(&self, f: F) -> R
    where
        F: Fn(&Self::Memory, f64) -> R,
    {
        assert!(self.lbd.is_none());
        f(&self.ema, self.sum / self.num as f64)
    }
    fn trend(&self) -> f64 {
        self.ema.get() * self.num as f64 / self.sum as f64
    }
}

impl RestartLBD {
    pub fn new(threshold: f64) -> Self {
        RestartLBD {
            sum: 0.0,
            num: 0,
            threshold,
            ema: Ema::new(EMA_FAST),
            lbd: None,
            result: false,
        }
    }
}

/// Glucose-style restart blocking condition w/o restart_steps
/// ### Implementing the original algorithm
///
/// ```ignore
///    blk = RestartASG::new(1.0 / 0.8);
///    blk.add(solver.num_assigns).commit();
///    if blk.eval(|ema, ave| blk.threshold * ave < ema.get()) {
///        blocking...
///    }
/// ```
/*
#[derive(Debug)]
pub struct RestartASG {
    pub max: usize,
    pub sum: usize,
    pub num: usize,
    pub threshold: f64,
    pub ema: Ema,
    asg: Option<usize>,
    result: bool,
}

impl ProgressEvaluatorIF<'_> for RestartASG {
    type Memory = Ema;
    type Item = usize;
    /*
    fn add(&mut self, item: Self::Item) -> &mut Self {
        assert!(self.asg.is_none());
        self.sum += item;
        self.num += 1;
        self.asg = Some(item);
        self
    }
    fn commit(&mut self) -> &mut Self {
        assert!(!self.asg.is_none());
        if let Some(a) = self.asg {
            self.ema.update(a as f64);
            self.asg = None;
            self.max = a.max(self.max);
        }
        self
    }
    */
    fn update(&mut self, item: Self::Item) {
        self.ema.update(item as f64);
        self.max = item.max(self.max);
    }
    fn update_with<F>(&mut self, f: F) -> &mut Self
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        assert!(self.asg.is_none());
        self.result = f(&self.ema, self.sum as f64 / self.num as f64);
        self
    }
    fn is_active(&self) -> bool {
        self.result
    }
    fn eval<F, R>(&self, f: F) -> R
    where
        F: Fn(&Self::Memory, f64) -> R,
    {
        assert!(self.asg.is_none());
        f(&self.ema, self.sum as f64 / self.num as f64)
    }
    fn trend(&self) -> f64 {
        self.ema.get() * self.num as f64 / self.sum as f64
    }
}

impl RestartASG {
    pub fn new(threshold: f64) -> Self {
        RestartASG {
            max: 0,
            sum: 0,
            num: 0,
            threshold,
            ema: Ema::new(EMA_FAST),
            asg: None,
            result: false,
        }
    }
}
 */

#[derive(Debug)]
pub struct RestartASG {
    pub max: usize,
    pub sum: usize,
    pub num: usize,
    pub threshold: f64,
    ema: Ema2,
    asg: Option<usize>,
    result: bool,
}

impl ProgressEvaluatorIF<'_> for RestartASG {
    type Memory = Ema2;
    type Item = usize;
    fn update(&mut self, item: Self::Item) {
        self.ema.update(item as f64);
        self.max = item.max(self.max);
    }
    fn update_with<F>(&mut self, f: F) -> &mut Self
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        assert!(self.asg.is_none());
        self.result = f(&self.ema, self.sum as f64 / self.num as f64);
        self
    }
    fn is_active(&self) -> bool {
        self.result
    }
    fn eval<F, R>(&self, f: F) -> R
    where
        F: Fn(&Self::Memory, f64) -> R,
    {
        assert!(self.asg.is_none());
        f(&self.ema, self.sum as f64 / self.num as f64)
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl RestartASG {
    pub fn new(threshold: f64) -> Self {
        RestartASG {
            max: 0,
            sum: 0,
            num: 0,
            threshold,
            ema: Ema2::new(EMA_SLOW).with_fast(EMA_FAST),
            asg: None,
            result: false,
        }
    }
    pub fn get(&self) -> f64 {
        self.ema.get()
    }
    pub fn get_fast(&self) -> f64 {
        self.ema.get_fast()
    }
    pub fn reset(&mut self) {
        self.max = 0;
        self.sum = 0;
        self.num = 0;
    }
}

#[derive(Debug)]
pub struct RestartLuby {
    pub num_conflict: f64,
    pub inc: f64,
    pub current_restart: usize,
    pub factor: f64,
    pub cnfl_cnt: f64,
    result: bool,
}

impl ProgressEvaluatorIF<'_> for RestartLuby {
    type Memory = usize;
    type Item = bool;
    fn update(&mut self, in_use: Self::Item) {
        if in_use {
            self.cnfl_cnt += 1.0;
            if self.num_conflict <= self.cnfl_cnt {
                self.cnfl_cnt = 0.0;
                self.current_restart += 1;
                self.num_conflict = luby(self.inc, self.current_restart) * self.factor;
                self.result = true;
            } else {
                self.result = false;
            }
        }
    }
    fn update_with<F>(&mut self, _f: F) -> &mut Self
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        if self.num_conflict <= self.cnfl_cnt {
            self.cnfl_cnt = 0.0;
            self.current_restart += 1;
            self.num_conflict = luby(self.inc, self.current_restart) * self.factor;
            self.result = true;
        } else {
            self.result = false;
        }
        self
    }
    fn is_active(&self) -> bool {
        self.result
    }
    fn eval<F, R>(&self, _f: F) -> R
    where
        F: Fn(&Self::Memory, f64) -> R,
    {
        panic!("RestartLuby doesn't implement check.");
    }
    fn trend(&self) -> f64 {
        0.0
    }
}

impl Default for RestartLuby {
    fn default() -> Self {
        RestartLuby {
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
            num_conflict: 0.0,
            inc,
            current_restart: 0,
            factor,
            cnfl_cnt: 0.0,
            result: false,
        }
    }
    pub fn initialize(&mut self) -> &mut Self {
        self.cnfl_cnt = 0.0;
        self.num_conflict = luby(self.inc, self.current_restart) * self.factor;
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

/// A superium of variables as a metrics of progress of search.
/// There were a various categories:
/// - assigned variable set, AVS
/// - assigned or cancelled variables, ACV
/// - superium of ACV (not being reset), SuA
/// - first UIPs, FUP
/// - superium of first UIPs, SuA
///
/// AVS was a variant of the present AGS. And it has no flag in Var::flag field.
#[derive(Debug)]
pub struct VarSet {
    pub flag: Flag,
    pub sum: usize,
    pub num: usize,
    pub diff: Option<f64>,
    pub diff_ema: Ema2,
    is_closed: bool,
    pub num_build: usize,
}

impl VarSetIF for VarSet {
    fn new(flag: Flag) -> Self {
        VarSet {
            flag,
            sum: 0,
            num: 0,
            diff: None,
            diff_ema: Ema2::new(EMA_SLOW * 2).with_fast(EMA_FAST * 16),
            is_closed: false,
            num_build: 1,
        }
    }
    fn remove(&self, v: &mut Var) {
        if v.is(self.flag) {
            v.turn_off(self.flag);
        }
    }
    fn reset(&mut self) {
        self.sum = 0;
        self.num = 0;
        self.diff = None;
        self.is_closed = false;
        self.diff_ema.reinitialize(0.0);
        self.num_build += 1;
    }
}

impl<'a> ProgressEvaluatorIF<'a> for VarSet {
    type Memory = Ema2;
    type Item = &'a mut Var;
    fn update(&mut self, v: Self::Item) {
        self.num += 1;
        if !v.is(self.flag) {
            v.turn_on(self.flag);
            self.sum += 1;
            self.diff_ema.update(1.0);
        } else {
            self.diff_ema.update(0.0);
        }
    }
    fn update_with<F>(&mut self, f: F) -> &mut Self
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        // assert!(self.diff.is_none());
        self.is_closed = f(&self.diff_ema, self.sum as f64 / self.num as f64);
        self
    }
    fn is_active(&self) -> bool {
        self.is_closed
    }
    fn eval<F, R>(&self, f: F) -> R
    where
        F: Fn(&Self::Memory, f64) -> R,
    {
        // assert!(self.diff.is_none());
        f(&self.diff_ema, self.sum as f64 / self.num as f64)
    }
    fn trend(&self) -> f64 {
        self.diff_ema.get() * self.num as f64 / self.sum as f64
    }
}

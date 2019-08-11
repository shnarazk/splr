use crate::propagator::AssignStack;
use crate::state::{Stat, State};
use crate::traits::*;
use crate::types::Flag;
use crate::var::{Var, VarDB};

// const CLOSE_THRD: f64 = 0.5; // 0.72;
const EMA_SLOW: usize = 8192; // 2 ^ 13; 2 ^ 15 = 32768
const EMA_FAST: usize = 64; // 2 ^ 6

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
        // if self.after_restart < 32 {
        //     self.restart_ratio.update(0.0);
        //     return false
        // }
        if let Some(t) = self.rst.cooling {
            if self.rst.fup.trend() < t {
                self.rst.cooling = None;
            } else {
                self.restart_ratio.update(0.0);
                return false;
            }
        }
        if 1.4 < self.rst.asg.trend() {
            self.rst.cooling = Some(0.95 * self.rst.fup.trend());
            return false;
        }

        // (0.8, 3.6) -- (1.2, 1.2)
        let restart = // 0.8 < self.rst.fup.trend() &&
            // self.rst.asg.trend() < 0.8
            8.4 - 6.0 * self.rst.fup.trend() < self.rst.lbd.trend()
            && 1.25 < self.rst.lbd.trend()
            ;
        /*
        let fract = 1.2 < self.rst.lbd.trend() && 1.2 < self.rst.fup.trend();
        if  fract {
            self.stats[Stat::RestartByAsg] += 1;
        }
        let still = 3.5 < self.rst.lbd.trend() && 0.8 < self.rst.fup.trend();
        if  still {
            self.stats[Stat::RestartByFUP] += 1;
        }
        let restart = fract || still;
         */

        /* else if self.rst.asg.should_restart() {
          // This is ant-blocking condition.
          // self.stats[Stat::BlockingByAsg] += 1;
          // false
        } */
        // if self.rst.asv.is_active() {
        //     self.stats[Stat::RestartByFUP] += 1;
        //     restart = false;
        // }
        // if self.rst.sua.is_active() {
        //     level2_restart = true;
        //     self.stats[Stat::RestartBySuA] += 1;
        // }

        if restart {
            self.rst.cooling = Some(0.9 * self.rst.fup.trend());
            asgs.cancel_until(vdb, 0);
            asgs.check_progress();
            self.restart_ratio.update(1.0);
            // No need to call remove nor reset for asv. It's memoryless. 
            if self.rst.fup.is_active() && false {
                for v in &mut vdb.vars[1..] {
                    if !v.is(Flag::ELIMINATED) {
                        // self.rst.acv.remove(v);
                        self.rst.fup.remove(v);
                    }
                }
                // self.rst.acv.reset();
                self.rst.fup.reset();
            }
            self.after_restart = 0;
            self.stats[Stat::Restart] += 1;
            // {
            //     let ra = self.stats[Stat::RestartByAsg];
            //     let rf = self.stats[Stat::RestartByFUP];
            //     if 0 < ra && 0 < rf {
            //         let s = self.config.var_activity_decay;
            //         let m = self.config.var_activity_d_max;
            //         let k = ra.max(rf) as f64 / (ra + rf) as f64;
            //         vdb.activity_decay = k * m + (1.0 - k) * s;
            //     }
            // }
            true
        } else if self.rst.fup.trend().log(10.0) < -2.0 {
            if self.num_vars - self.num_solved_vars - self.num_eliminated_vars < 2 * self.rst.fup.sum {
            self.use_luby_restart = true;
            } else {
                for v in &mut vdb.vars[1..] {
                    if !v.is(Flag::ELIMINATED) {
                        self.rst.fup.remove(v);
                    }
                }
                self.rst.fup.reset();
            }
            false
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
    pub cooling: Option<f64>,
    pub lbd: RestartLBD,
    pub asg: RestartASG,
    // pub asv: VarSet,
    // pub acv: VarSet,
    // pub sua: VarSet,
    pub fup: VarSet,
    // pub suf: VarSet,
}

impl ProgressEvaluatorPack {
    pub fn new(n: usize) -> ProgressEvaluatorPack {
        let _scale: f64 = (n as f64).log(2f64);
        ProgressEvaluatorPack {
            cooling: None,
            lbd: RestartLBD::new(0.1),
            asg: RestartASG::new(0.1),
            // asv: VarSet::new(None, CLOSE_THRD * scale),
            // acv: VarSet::new(Some(Flag::ACV), CLOSE_THRD * scale),
            // sua: VarSet::new(Some(Flag::SUA), CLOSE_THRD * scale),
            fup: VarSet::new(Some(Flag::FUP), 0.05),
            // suf: VarSet::new(Some(Flag::SUF), CLOSE_THRD),
        }
    }
}


/// Glucose original (or Lingering-style) forcing restart condition
/// ### Implementing the original algorithm
///
/// ```ignore
///    rst = RestartLBD::new(1.4);
///    rst.add(learnt.lbd()).commit();
///    if rst.update(|ema, ave| rst.threshold * ave < ema.get()).is_active() {
///        restarting...
///    }
/// ```
///
/// ### Implementing an EMA-pair-based variant
///
/// ```ignore
///    rst = RestartLBD2::new(1.4);
///    rst.add(learnt.lbd()).commit();
///    if rst.update(|ema, _| rst.threshold * ema.get() < ema.get_fast()).is_active() {
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
    fn commit(&mut self) -> &mut Self {
        assert!(!self.lbd.is_none());
        if let Some(lbd) = self.lbd {
            self.ema.update(lbd as f64);
            self.lbd = None;
        }
        self
    }
    fn update<F>(&mut self, f: F) -> &mut Self
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        assert!(self.lbd.is_none());
        if 0 < self.timer {
            self.timer -= 1;
        } else {
            self.result = f(&self.ema, self.sum / self.num as f64);
            if self.result {
                self.timer = 50;
            }
        }
        self
    }
    fn is_active(&self) -> bool {
        0 < self.timer && self.result
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
///    blk.add(solver.num_assigns).commit();
///    if blk.update(|ema, ave| blk.threshold * ave < ema.get()).is_active() {
///        blocking...
///    }
/// ```
/// ### Implementing an EMA-pair-based variant
///
/// ```ignore
///    blk = RestartASG2::new(1.0 / 0.8);
///    blk.add(solver.num_assigns).commit();
///    if blk.update(|ema, _| blk.threshold * ema.get() < ema.get_fast()).is_active() {
///        blocking...
///    }
/// ```
#[derive(Debug)]
pub struct RestartASG {
    pub max: usize,
    pub sum: usize,
    pub num: usize,
    pub threshold: f64,
    pub ema: Ema,
    asg: Option<usize>,
    result: bool,
    // timer: usize,
}

impl ProgressEvaluatorIF<'_> for RestartASG {
    type Memory = Ema;
    type Item = usize;
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
    fn update<F>(&mut self, f: F) -> &mut Self
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        assert!(self.asg.is_none());
        self.result = f(&self.ema, self.sum as f64 / self.num as f64);
        // if 0 < self.timer {
        //     self.timer -= 1;
        // } else {
        //
        //     if self.result {
        //         self.timer = 50;
        //     }
        // }
        self
    }
    fn is_active(&self) -> bool {
        // 0 < self.timer &&
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
            ema: Ema::new(200),
            asg: None,
            result: false,
            // timer: 20,
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
    fn commit(&mut self) -> &mut Self {
        self
    }
    fn update<F>(&mut self, _f: F) -> &mut Self
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

#[derive(Debug)]
pub struct VarSet {
    pub flag: Option<Flag>,
    pub sum: usize,
    pub cnt: usize,
    pub diff: Option<f64>,
    pub diff_ema: Ema2,
    pub threshold: f64,
    is_closed: bool,
}

impl VarSetIF for VarSet {
    fn new(flag: Option<Flag>, threshold: f64) -> Self {
        VarSet {
            flag,
            sum: 0,
            cnt: 0,
            diff: None,
            diff_ema: Ema2::new(EMA_SLOW).with_fast(EMA_FAST).initialize1(),
            is_closed: false,
            threshold,
        }
    }
    fn remove(&self, v: &mut Var) {
        if let Some(flag) = self.flag {
            if v.is(flag) {
                v.turn_off(flag);
            }
        }
    }
    fn reset(&mut self) {
        self.sum = 0;
        self.cnt = 0;
        self.diff = None;
        self.is_closed = false;
        self.diff_ema.reinitialize1();
    }
}

impl<'a> ProgressEvaluatorIF<'a> for VarSet {
    type Memory = Ema2;
    type Item = &'a mut Var;
    fn add(&mut self, v: Self::Item) -> &mut Self {
        self.cnt += 1;
        match self.flag {
            Some(flag) => {
                if !v.is(flag) {
                    v.turn_on(flag);
                    self.sum += 1;
                    self.diff = Some(self.diff.map_or(1.0, |v| v + 1.0));
                } else if self.diff.is_none() {
                    self.diff = Some(0.0);
                }
            }
            None => {
                self.sum += 1;
                self.diff = Some(self.diff.map_or(1.0, |v| v + 1.0));
            }
        }
        self
    }
    fn commit(&mut self) -> &mut Self {
        if let Some(diff) = self.diff {
            self.diff_ema.update(diff);
            self.diff = None;
        } else {
            panic!("VarSet {:?}::commit, self.diff is None", self.flag);
        }
        self
    }
    fn update<F>(&mut self, f: F) -> &mut Self
    where
        F: Fn(&Self::Memory, f64) -> bool,
    {
        // assert!(self.diff.is_none());
        self.is_closed = f(&self.diff_ema, self.sum as f64 / self.cnt as f64);
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
        f(&self.diff_ema, self.threshold)
    }
    fn trend(&self) -> f64 {
        self.diff_ema.get() * self.cnt as f64 / self.sum as f64
    }
}

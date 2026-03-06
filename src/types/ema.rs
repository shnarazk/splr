/// API for observing EMA.
pub trait EmaIF {
    /// return the current value.
    fn get_fast(&self) -> f64 {
        unimplemented!()
    }
    /// return the current value.
    fn get(&self) -> f64 {
        self.get_fast()
    }
    fn get_slow(&self) -> f64 {
        unimplemented!()
    }
    /// return a ratio of short / long statistics.
    fn trend(&self) -> f64 {
        unimplemented!()
    }
}

pub trait EmaSingleIF: EmaIF {
    /// return the current value.
    fn get(&self) -> f64 {
        self.get_fast()
    }
}

/// API for Exponential Moving Average, EMA, like `get`, `reset`, `update` and so on.
pub trait EmaMutIF: EmaIF {
    /// the type of the argument of `update`.
    type Input;
    /// reset internal data.
    fn reset_to(&mut self, _: f64) {}
    fn reset_fast(&mut self) {}
    fn reset_slow(&mut self) {}
    /// catch up with the current state.
    fn update(&mut self, x: Self::Input);
    /// return a view.
    fn as_view(&self) -> &EmaView;
    /// set value.
    fn set_value(&mut self, _x: f64) {}
}

#[derive(Clone, Debug)]
pub struct EmaView {
    fast: f64,
    slow: f64,
}

impl EmaIF for EmaView {
    fn get_fast(&self) -> f64 {
        self.fast
    }
    fn get_slow(&self) -> f64 {
        self.slow
    }
    fn trend(&self) -> f64 {
        self.fast / self.slow
    }
}

/// Exponential Moving Average, with a calibrator if feature `EMA_calibration` is on.
#[derive(Clone, Debug)]
pub struct Ema {
    val: EmaView,
    #[cfg(feature = "EMA_calibration")]
    cal: f64,
    sca: f64,
}

impl EmaIF for Ema {
    #[cfg(feature = "EMA_calibration")]
    fn get_fast(&self) -> f64 {
        self.val.fast / self.cal
    }
    #[cfg(not(feature = "EMA_calibration"))]
    fn get_fast(&self) -> f64 {
        self.val.fast
    }
    fn get_slow(&self) -> f64 {
        unimplemented!()
    }
    fn trend(&self) -> f64 {
        unimplemented!()
    }
}

impl EmaMutIF for Ema {
    type Input = f64;
    #[cfg(not(feature = "EMA_calibration"))]
    fn update(&mut self, x: Self::Input) {
        self.val.fast = self.sca * x + (1.0 - self.sca) * self.val.fast;
    }
    #[cfg(feature = "EMA_calibration")]
    fn update(&mut self, x: Self::Input) {
        self.val.fast = self.sca * x + (1.0 - self.sca) * self.val.fast;
        self.cal = self.sca + (1.0 - self.sca) * self.cal;
    }
    fn as_view(&self) -> &EmaView {
        &self.val
    }
    fn set_value(&mut self, x: f64) {
        self.val.fast = x;
        self.val.slow = x;
    }
}

impl Ema {
    pub fn new(s: usize) -> Ema {
        Ema {
            val: EmaView {
                fast: 0.0,
                slow: 0.0,
            },
            #[cfg(feature = "EMA_calibration")]
            cal: 0.0,
            sca: 1.0 / (s as f64),
        }
    }
    /// set value.
    pub fn with_value(mut self, x: f64) -> Ema {
        self.val.fast = x;
        self.val.slow = x;
        self
    }
}

/// Exponential Moving Average pair, with a calibrator if feature `EMA_calibration` is on.
#[derive(Clone, Debug)]
pub struct Ema2 {
    ema: EmaView,
    #[cfg(feature = "EMA_calibration")]
    calf: f64,
    #[cfg(feature = "EMA_calibration")]
    cals: f64,
    fe: f64,
    se: f64,
}

impl EmaIF for Ema2 {
    #[cfg(feature = "EMA_calibration")]
    fn get_fast(&self) -> f64 {
        self.ema.fast / self.calf
    }
    #[cfg(not(feature = "EMA_calibration"))]
    fn get_fast(&self) -> f64 {
        self.ema.fast
    }
    #[cfg(feature = "EMA_calibration")]
    fn get_slow(&self) -> f64 {
        self.ema.slow / self.calf
    }
    #[cfg(not(feature = "EMA_calibration"))]
    fn get_slow(&self) -> f64 {
        self.ema.slow
    }
    #[cfg(feature = "EMA_calibration")]
    fn trend(&self) -> f64 {
        self.ema.fast / self.ema.slow * (self.cals / self.calf)
    }
    #[cfg(not(feature = "EMA_calibration"))]
    fn trend(&self) -> f64 {
        self.ema.fast / self.ema.slow
    }
}

impl EmaMutIF for Ema2 {
    type Input = f64;
    #[cfg(not(feature = "EMA_calibration"))]
    fn update(&mut self, x: Self::Input) {
        self.ema.fast = self.fe * x + (1.0 - self.fe) * self.ema.fast;
        self.ema.slow = self.se * x + (1.0 - self.se) * self.ema.slow;
    }
    #[cfg(feature = "EMA_calibration")]
    fn update(&mut self, x: Self::Input) {
        self.ema.fast = self.fe * x + (1.0 - self.fe) * self.ema.fast;
        self.ema.slow = self.se * x + (1.0 - self.se) * self.ema.slow;
        self.calf = self.fe + (1.0 - self.fe) * self.calf;
        self.cals = self.se + (1.0 - self.se) * self.cals;
    }
    fn reset_to(&mut self, val: f64) {
        self.ema.fast = val;
    }
    #[cfg(not(feature = "EMA_calibration"))]
    fn reset_fast(&mut self) {
        self.ema.fast = self.ema.slow;
    }
    #[cfg(feature = "EMA_calibration")]
    fn reset_fast(&mut self) {
        self.ema.fast = self.ema.slow;
        self.calf = self.cals;
    }
    #[cfg(not(feature = "EMA_calibration"))]
    fn reset_slow(&mut self) {
        self.ema.slow = self.ema.fast;
    }
    #[cfg(feature = "EMA_calibration")]
    fn reset_slow(&mut self) {
        self.ema.slow = self.ema.fast;
        self.cals = self.calf;
    }
    fn as_view(&self) -> &EmaView {
        &self.ema
    }
}

impl Ema2 {
    pub fn new(len: usize) -> Ema2 {
        Ema2 {
            ema: EmaView {
                fast: 0.0,
                slow: 0.0,
            },
            #[cfg(feature = "EMA_calibration")]
            calf: 0.0,
            #[cfg(feature = "EMA_calibration")]
            cals: 0.0,
            fe: 1.0 / (len as f64),
            se: 1.0 / (len as f64),
        }
    }
    // set secondary EMA parameter
    pub fn with_slow(mut self, s: usize) -> Ema2 {
        self.se = 1.0 / (s as f64);
        self
    }
    pub fn get_slow(&self) -> f64 {
        self.ema.slow // / self.calf
    }
    /// set value.
    pub fn with_value(mut self, x: f64) -> Self {
        self.ema.fast = x;
        self.ema.slow = x;
        #[cfg(feature = "EMA_calibration")]
        {
            self.calf = 1.0;
            self.cals = 1.0;
        }
        self
    }
}

/// Ema of Sequence of usize
#[derive(Clone, Debug)]
pub struct EmaSU {
    last: f64,
    ema: Ema,
}

impl EmaIF for EmaSU {
    fn get_fast(&self) -> f64 {
        self.ema.get_fast()
    }
    fn get_slow(&self) -> f64 {
        unimplemented!()
    }
    fn trend(&self) -> f64 {
        unimplemented!()
    }
}

impl EmaMutIF for EmaSU {
    type Input = usize;
    fn update(&mut self, x: Self::Input) {
        let diff: f64 = x as f64 - self.last;
        self.ema.update(diff);
        self.last = x as f64;
    }
    fn as_view(&self) -> &EmaView {
        self.ema.as_view()
    }
}

impl EmaSU {
    pub fn new(s: usize) -> Self {
        EmaSU {
            last: 0.0,
            ema: Ema::new(s),
        }
    }
    pub fn update_base(&mut self, x: usize) {
        self.last = x as f64;
    }
    pub fn get_ema(&self) -> &Ema {
        &self.ema
    }
}

/// Equally-Weighted-Average, namely, Average
#[derive(Clone, Debug)]
pub struct Ewa<const N: usize = 32> {
    ema: EmaView,
    pool: [f64; N],
    last: usize,
}

impl<const N: usize> EmaIF for Ewa<N> {
    fn get_fast(&self) -> f64 {
        self.ema.fast
    }
}

impl<const N: usize> EmaMutIF for Ewa<N> {
    type Input = f64;
    fn update(&mut self, x: Self::Input) {
        self.ema.fast -= self.pool[self.last];
        let val = x / N as f64;
        self.ema.fast += val;
        self.pool[self.last] = val;
        self.last = (self.last + 1) % N;
    }
    fn as_view(&self) -> &EmaView {
        &self.ema
    }
}

impl<const N: usize> Ewa<N> {
    pub fn new(initial: f64) -> Self {
        Ewa::<N> {
            ema: EmaView {
                fast: initial,
                slow: initial,
            },
            pool: [initial; N],
            last: 0,
        }
    }
}

/// Exponential Moving Average pair, with a calibrator if feature `EMA_calibration` is on.
#[derive(Clone, Debug)]
pub struct Ewa2<const N: usize> {
    ema: EmaView,
    pool: [f64; N],
    last: usize,
    #[cfg(feature = "EMA_calibration")]
    cals: f64,
    se: f64,
    sx: f64,
}

impl<const N: usize> EmaIF for Ewa2<N> {
    fn get_fast(&self) -> f64 {
        self.ema.fast
    }
    #[cfg(not(feature = "EMA_calibration"))]
    fn trend(&self) -> f64 {
        self.ema.fast / self.ema.slow
    }
    #[cfg(feature = "EMA_calibration")]
    fn trend(&self) -> f64 {
        self.ema.fast * self.cals / self.slow
    }
}

impl<const N: usize> EmaMutIF for Ewa2<N> {
    type Input = f64;
    fn update(&mut self, x: Self::Input) {
        self.ema.fast -= self.pool[self.last];
        let val = x / N as f64;
        self.ema.fast += val;
        self.pool[self.last] = val;
        self.last = (self.last + 1) % N;
        self.ema.slow = self.se * x + self.sx * self.ema.slow;
        #[cfg(feature = "EMA_calibration")]
        {
            self.cals = self.se + self.sx * self.cals;
        }
    }
    fn reset_to(&mut self, val: f64) {
        self.ema.fast = val;
    }
    #[cfg(not(feature = "EMA_calibration"))]
    fn reset_fast(&mut self) {
        unimplemented!();
    }
    #[cfg(feature = "EMA_calibration")]
    fn reset_fast(&mut self) {
        unimplemented!();
    }
    #[cfg(not(feature = "EMA_calibration"))]
    fn reset_slow(&mut self) {
        self.ema.slow = self.ema.fast;
    }
    #[cfg(feature = "EMA_calibration")]
    fn reset_slow(&mut self) {
        self.ema.slow = self.fast.get();
        self.cals = self.calf;
    }
    fn as_view(&self) -> &EmaView {
        &self.ema
    }
}

impl<const N: usize> Ewa2<N> {
    pub fn new(initial: f64) -> Ewa2<N> {
        Ewa2::<N> {
            ema: EmaView {
                fast: initial,
                slow: initial,
            },
            pool: [initial; N],
            last: 0,
            #[cfg(feature = "EMA_calibration")]
            cals: initial,
            se: 1.0 / (N as f64),
            sx: 1.0 - 1.0 / (N as f64),
        }
    }
    // set secondary EMA parameter
    pub fn with_slow(mut self, s: usize) -> Self {
        self.se = 1.0 / (s as f64);
        self.sx = 1.0 - self.se;
        self
    }
}

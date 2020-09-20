use {crate::types::*, std::fmt};

#[derive(Debug)]
pub struct ProgressACT {
    pub ema: Ema2,
    num: usize,
    sum: f64,
}

impl Default for ProgressACT {
    fn default() -> ProgressACT {
        ProgressACT {
            ema: Ema2::new(1),
            num: 0,
            sum: 0.0,
        }
    }
}

impl fmt::Display for ProgressACT {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ProgressACT[val:{}]", self.ema.get(),)
    }
}

impl Instantiate for ProgressACT {
    fn instantiate(_config: &Config, _: &CNFDescription) -> Self {
        ProgressACT {
            ema: Ema2::new(10_000).with_slow(1_000_000),
            ..ProgressACT::default()
        }
    }
}

impl EmaIF for ProgressACT {
    type Input = f64;
    fn update(&mut self, val: Self::Input) {
        self.num += 1;
        self.sum += val;
    }
    fn get(&self) -> f64 {
        self.ema.get()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl ProgressACT {
    pub fn shift(&mut self) {
        if 0 < self.num {
            self.ema.update(self.sum / self.num as f64);
            self.num = 0;
        }
        self.sum = 0.0;
    }
}

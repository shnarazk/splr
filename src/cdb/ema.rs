use crate::types::*;

const LBD_EMA_LEN: usize = 16;
const LBD_EMA_SLOW: usize = 8192;

/// An EMA of learnt clauses' LBD, used for forcing restart.
#[derive(Clone, Debug)]
pub struct ProgressLBD {
    ema: Ema2,
    num: usize,
    sum: usize,
}

impl Default for ProgressLBD {
    fn default() -> ProgressLBD {
        ProgressLBD {
            ema: Ema2::new(LBD_EMA_LEN).with_slow(LBD_EMA_SLOW),
            num: 0,
            sum: 0,
        }
    }
}

impl Instantiate for ProgressLBD {
    fn instantiate(_config: &Config, _: &CNFDescription) -> Self {
        ProgressLBD {
            ema: Ema2::new(LBD_EMA_LEN).with_slow(LBD_EMA_SLOW),
            ..ProgressLBD::default()
        }
    }
}

impl EmaIF for ProgressLBD {
    fn get_fast(&self) -> f64 {
        self.ema.get_fast()
    }
    fn get_slow(&self) -> f64 {
        self.ema.get_fast()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl EmaMutIF for ProgressLBD {
    type Input = DecisionLevel;
    fn update(&mut self, d: Self::Input) {
        self.num += 1;
        self.sum += d as usize;
        self.ema.update(d as f64);
    }
    fn reset_to(&mut self, val: f64) {
        self.ema.reset_to(val);
    }
    fn as_view(&self) -> &EmaView {
        self.ema.as_view()
    }
}

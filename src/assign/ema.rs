use crate::types::*;

const ASG_EMA_LEN: usize = 16;
const ASG_EMA_SLOW: usize = 8192;

/// An assignment history used for blocking restart.
#[derive(Clone, Debug)]
pub struct ProgressASG {
    ema: Ema2,
}

impl Default for ProgressASG {
    fn default() -> ProgressASG {
        ProgressASG {
            ema: Ema2::new(ASG_EMA_LEN).with_slow(ASG_EMA_SLOW),
        }
    }
}

impl Instantiate for ProgressASG {
    fn instantiate(_config: &Config, _cnf: &CNFDescription) -> Self {
        ProgressASG {
            ema: Ema2::new(ASG_EMA_LEN).with_slow(ASG_EMA_SLOW),
        }
    }
}

impl EmaIF for ProgressASG {
    fn get_fast(&self) -> f64 {
        self.ema.get()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl EmaMutIF for ProgressASG {
    type Input = usize;
    fn update(&mut self, n: usize) {
        self.ema.update(n as f64);
    }
    fn as_view(&self) -> &EmaView {
        self.ema.as_view()
    }
}

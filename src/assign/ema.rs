use crate::types::*;

const ASG_EWA_LEN: usize = 16;
const ASG_EWA_SLOW: usize = 8192;

/// An assignment history used for blocking restart.
#[derive(Clone, Debug)]
pub struct ProgressASG {
    ema: Ewa2<ASG_EWA_LEN>,
}

impl Default for ProgressASG {
    fn default() -> ProgressASG {
        ProgressASG {
            ema: Ewa2::<ASG_EWA_LEN>::new(0.0),
        }
    }
}

impl Instantiate for ProgressASG {
    fn instantiate(_config: &Config, _cnf: &CNFDescription) -> Self {
        ProgressASG {
            ema: Ewa2::new(0.0).with_slow(ASG_EWA_SLOW),
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

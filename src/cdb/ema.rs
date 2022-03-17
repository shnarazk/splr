use crate::types::*;

const LBD_EWA_LEN: usize = 16;

/// An EMA of learnt clauses' LBD, used for forcing restart.
#[derive(Clone, Debug)]
pub struct ProgressLBD {
    ema: Ewa2<LBD_EWA_LEN>,
    num: usize,
    sum: usize,
}

impl Default for ProgressLBD {
    fn default() -> ProgressLBD {
        ProgressLBD {
            ema: Ewa2::<LBD_EWA_LEN>::new(0.0),
            num: 0,
            sum: 0,
        }
    }
}

impl Instantiate for ProgressLBD {
    fn instantiate(config: &Config, _: &CNFDescription) -> Self {
        ProgressLBD {
            ema: Ewa2::new(0.0).with_slow(config.rst_lbd_slw),
            ..ProgressLBD::default()
        }
    }
}

impl EmaIF for ProgressLBD {
    fn get_fast(&self) -> f64 {
        self.ema.get_fast()
    }
    fn trend(&self) -> f64 {
        self.ema.trend()
    }
}

impl EmaMutIF for ProgressLBD {
    type Input = u16;
    fn update(&mut self, d: Self::Input) {
        self.num += 1;
        self.sum += d as usize;
        self.ema.update(d as f64);
    }
    fn as_view(&self) -> &EmaView {
        self.ema.as_view()
    }
}

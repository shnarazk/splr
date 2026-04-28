use crate::types::*;

/// An EMA of learnt clauses' LBD, used for forcing restart.
#[derive(Clone, Debug, Default)]
pub struct ProgressLBD {
    ema: Ema2,
    num: usize,
    sum: usize,
}

impl Instantiate for ProgressLBD {
    fn instantiate(_config: &Config, _: &CNFDescription) -> Self {
        ProgressLBD {
            ema: Ema2::default(),
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
    type Input = u16;
    fn update(&mut self, d: Self::Input) {
        self.num += 1;
        self.sum += d as usize;
        self.ema.update(d as f64);
    }
    fn reset_to(&mut self, val: f64) {
        self.ema.reset_to(val);
    }
    fn set_spans(&mut self, f: f64, s: f64) {
        self.ema.set_spans(f, s);
    }
    fn rescale_span(&mut self, r: f64) {
        self.ema.rescale_span(r)
    }
    fn as_view(&self) -> &EmaView {
        self.ema.as_view()
    }
}

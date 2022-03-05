/// An implementation of CaDiCaL-style blocker.
/// I define it as a 'search mode', or stage, changer.
/// A stage is a span sharing same restart parameters.
/// And it also define the interval of clause reduction.
use splr_luby::LubySeries;

#[derive(Clone, Debug, Default)]
pub struct StageManager {
    age: usize,
    scale: usize,
    luby_iter: LubySeries,
    luby: usize,
    threshold: usize,
}

impl StageManager {
    pub fn new(scale: usize) -> Self {
        StageManager {
            age: 1,
            scale,
            luby_iter: LubySeries::default(),
            luby: 1,
            threshold: scale,
        }
    }
    pub fn prepare_new_stage(&mut self, rescale: usize, now: usize) {
        self.threshold = now + self.next_span(rescale);
    }
    pub fn stage_ended(&self, now: usize) -> bool {
        self.threshold < now
    }
    pub fn next_span(&mut self, rescale: usize) -> usize {
        self.scale = rescale;
        self.luby = self.luby_iter.next_unchecked();
        if self.luby == 1 {
            self.age += 1;
        }
        self.current_span()
    }
    /// return the number of conflicts in the current stage
    pub fn current_span(&self) -> usize {
        self.age * self.scale * self.luby
    }
    pub fn num_reducible(&self) -> usize {
        self.current_span() - self.scale / 2
    }
    #[allow(dead_code)]
    fn update(&mut self) {
        self.age += 1;
    }
    pub fn num_stage(&self) -> usize {
        self.age
    }
    /// return the factor of the current span
    pub fn luby(&self) -> usize {
        self.luby
    }
    /// return the maximum factor so far.
    pub fn max(&self) -> usize {
        self.luby_iter.max_value()
    }
}

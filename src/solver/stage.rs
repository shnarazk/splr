/// An implementation of CaDiCaL-style blocker.
/// I define it as a 'search mode', or stage, changer.
/// A stage is a span sharing same restart parameters.
/// And it also define the interval of clause reduction.
use splr_luby::LubySeries;

#[derive(Clone, Debug, Default)]
pub struct StageManager {
    cycle: usize,
    stage: usize,
    scale: usize,
    luby_iter: LubySeries,
    luby: usize,
    threshold: usize,
}

impl StageManager {
    pub fn new(scale: usize) -> Self {
        StageManager {
            cycle: 1,
            stage: 0,
            scale,
            luby_iter: LubySeries::default(),
            luby: 1,
            threshold: scale,
        }
    }
    pub fn initialize(&mut self, scale: usize) {
        self.cycle = 1;
        self.scale = scale;
        self.luby = 1;
        self.threshold = scale;
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
        self.stage += 1;
        if self.luby == 1 {
            self.cycle += 1;
        }
        self.current_span()
    }
    /// return the number of conflicts in the current stage
    pub fn current_span(&self) -> usize {
        self.cycle * self.scale * self.luby
    }
    pub fn num_reducible(&self) -> usize {
        self.current_span() - self.scale / 2
    }
    pub fn current_stage(&self) -> usize {
        self.stage
    }
    pub fn current_cycle(&self) -> usize {
        self.cycle
    }
    /// return the factor of the current span
    pub fn current_scale(&self) -> usize {
        self.luby
    }
    /// return the maximum factor so far.
    pub fn max_scale(&self) -> usize {
        self.luby_iter.max_value()
    }
}

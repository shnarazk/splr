/// An implementation of CaDiCaL-style blocker.
/// I define it as a 'search mode', or stage, changer.
/// A stage is a span sharing same restart parameters.
/// And it also define the interval of clause reduction.
use crate::types::*;

trait NaturalNumberGenerator: Clone + Default {
    fn next_number(&mut self) -> usize;
    fn reset(&mut self);
}

impl NaturalNumberGenerator for LubySeries {
    fn next_number(&mut self) -> usize {
        self.next_unchecked()
    }
    fn reset(&mut self) {
        self.reset_values()
    }
}

#[derive(Clone, Debug, Default)]
pub struct StageManager {
    cycle: usize,
    stage: usize,
    segment: usize,
    unit_size: usize,
    generator: LubySeries,
    max_scale_of_segment: usize,
    scale: usize,
    end_of_stage: usize,
    next_is_new_segment: bool,
    cycle_starting_stage: usize,
    segment_starting_stage: usize,
    segment_starting_cycle: usize,
    span_base: f64,
    span_ema: Ema,
}

impl Instantiate for StageManager {
    fn instantiate(_: &Config, _cnf: &CNFDescription) -> StageManager {
        let unit_size = 8;
        StageManager {
            unit_size,
            max_scale_of_segment: 1,
            scale: 1,
            end_of_stage: unit_size,
            next_is_new_segment: false,
            span_ema: Ema::new(4).with_value(1.0),
            ..StageManager::default()
        }
    }
    fn handle(&mut self, _: SolverEvent) {
        unimplemented!();
    }
}

impl StageManager {
    pub fn new(_unit_size: usize) -> Self {
        let unit_size: usize = 8;
        StageManager {
            cycle: 0,
            stage: 0,
            segment: 0,
            unit_size,
            generator: LubySeries::default(),
            max_scale_of_segment: 1,
            scale: 1,
            end_of_stage: unit_size,
            next_is_new_segment: false,
            cycle_starting_stage: 0,
            segment_starting_stage: 0,
            segment_starting_cycle: 0,
            span_base: 0.0,
            span_ema: Ema::new(4).with_value(1.0),
        }
    }
    pub fn initialize(&mut self, _unit_size: usize) {
        // self.generator.reset();
        self.scale = 1;
        self.stage = 0;
        self.cycle = 0;
        self.segment = 0;
        self.unit_size = 8;
        self.max_scale_of_segment = 1;
        self.end_of_stage = self.unit_size;
        self.next_is_new_segment = true;
    }
    pub fn reset(&mut self) {
        self.generator.reset();
        self.scale = 1;
        self.stage = 0;
        self.cycle = 0;
        self.segment = 0;
        self.max_scale_of_segment = 1;
        self.end_of_stage = self.unit_size;
        self.next_is_new_segment = true;
    }
    /// returns:
    /// - Some(true): it's a beginning of a new cycle and a new segment, a 2nd-level group.
    /// - Some(false): a beginning of a new cycle.
    /// - None: the other case.
    pub fn prepare_new_stage(&mut self, now: usize) -> Option<bool> {
        let mut new_cycle = false;
        let mut new_segment = false;
        self.scale = self.generator.next_number();
        self.span_ema.update(4.0 + (self.scale as f64).powf(0.75));
        self.stage += 1;
        if self.scale == 1 {
            self.cycle += 1;
            self.cycle_starting_stage = self.stage;
            new_cycle = true;
            if self.next_is_new_segment {
                self.segment += 1;
                self.max_scale_of_segment *= 2;
                self.next_is_new_segment = false;
                self.segment_starting_stage = self.stage;
                self.segment_starting_cycle = self.cycle;
                new_segment = true;
            }
        }
        if self.max_scale_of_segment == self.scale {
            self.next_is_new_segment = true;
        }
        self.end_of_stage = now + self.span_ema.get() as usize;
        new_cycle.then_some(new_segment)
    }
    pub fn stage_ended(&self, now: usize) -> bool {
        self.end_of_stage <= now
    }
    pub fn to_stage_end(&self, now: usize) -> i32 {
        self.end_of_stage as i32 - now as i32
    }
    /// returns the number of conflicts in the current stage
    /// Note: we need not to make a strong correlation between this value and
    /// scale defined by Luby series. So this is fine.
    pub fn current_span(&self) -> f64 {
        self.span_ema.get()
    }
    pub fn current_stage(&self) -> usize {
        self.stage
    }
    pub fn current_cycle(&self) -> usize {
        self.cycle
    }
    /// returns the scaling factor used in the current span
    pub fn current_scale(&self) -> usize {
        self.scale
    }
    /// returns the current index for the level 2 segments
    pub fn current_segment(&self) -> usize {
        self.segment
    }
    /// returns the maximum factor so far.
    /// None: `luby_iter.max_value` holds the maximum value so far.
    /// This means it is the value found at the last segment.
    /// So the current value should be the next value, which is the double.
    pub fn max_scale(&self) -> usize {
        self.max_scale_of_segment
    }
    /// returns (0, 1]
    pub fn segment_progress_ratio(&self) -> f64 {
        (2 * (self.cycle - self.segment_starting_cycle + 1)) as f64
            / self.max_scale_of_segment as f64
    }
    pub fn cycle_starting_stage(&self) -> usize {
        self.cycle_starting_stage
    }
    pub fn segment_starting_cycle(&self) -> usize {
        self.segment_starting_cycle
    }
    pub fn segment_starting_stage(&self) -> usize {
        self.segment_starting_stage
    }
    pub fn set_unit_size(&mut self, _size: usize) {
        // self.unit_size = size;
    }
    pub fn set_span_base(&mut self, span_base: f64) {
        self.span_base = span_base;
    }
    /// returns a recommending number of redicible learnt clauses, based on
    /// the length of span.
    pub fn num_reducible(&self, reducing_factor: f64) -> usize {
        let span: f64 = self.span_ema.get();
        let keep = span.powf(1.0 - reducing_factor) as usize;
        (span as usize).saturating_sub(keep)
    }
}

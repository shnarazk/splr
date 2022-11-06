/// An implementation of CaDiCaL-style blocker.
/// I define it as a 'search mode', or stage, changer.
/// A stage is a span sharing same restart parameters.
/// And it also define the interval of clause reduction.
use crate::types::*;

#[derive(Clone, Debug, Default)]
pub struct StageManager {
    cycle: usize,
    stage: usize,
    segment: usize,
    unit_size: usize,
    luby_iter: LubySeries,
    max_scale_of_segment: usize,
    scale: usize,
    end_of_stage: usize,
    next_is_new_segment: bool,
    cycle_starting_stage: usize,
    segment_starting_stage: usize,
    segment_starting_cycle: usize,
}

impl Instantiate for StageManager {
    fn instantiate(_: &Config, cnf: &CNFDescription) -> StageManager {
        let unit_size = (cnf.num_of_variables as f64).sqrt() as usize;
        StageManager {
            unit_size,
            max_scale_of_segment: 1,
            scale: 1,
            end_of_stage: unit_size,
            next_is_new_segment: false,
            ..StageManager::default()
        }
    }
    fn handle(&mut self, _: SolverEvent) {}
}

impl StageManager {
    pub fn new(unit_size: usize) -> Self {
        StageManager {
            cycle: 0,
            stage: 0,
            segment: 0,
            unit_size,
            luby_iter: LubySeries::default(),
            max_scale_of_segment: 1,
            scale: 1,
            end_of_stage: unit_size,
            next_is_new_segment: false,
            cycle_starting_stage: 0,
            segment_starting_stage: 0,
            segment_starting_cycle: 0,
        }
    }
    pub fn initialize(&mut self, unit_size: usize) {
        self.cycle = 0;
        self.unit_size = unit_size;
        self.scale = 1;
        self.max_scale_of_segment = 1;
        self.end_of_stage = unit_size;
        self.next_is_new_segment = true;
    }
    pub fn reset(&mut self) {
        self.cycle = 0;
        self.scale = 1;
        self.max_scale_of_segment = 1;
        self.end_of_stage = self.unit_size;
        self.next_is_new_segment = true;
    }
    /// returns:
    /// - Some(true): it's a beginning of a new cycle and a new segment, a 2nd-level group.
    /// - Some(false): a beginning of a new cycle.
    /// - None: the other case.
    pub fn prepare_new_stage(&mut self, rescale: usize, now: usize) -> Option<bool> {
        self.unit_size = rescale;
        let mut new_cycle = false;
        let mut new_segment = false;
        self.scale = self.luby_iter.next_unchecked();
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
        let span = self.current_span();
        self.end_of_stage = now + span;
        new_cycle.then_some(new_segment)
    }
    pub fn stage_ended(&self, now: usize) -> bool {
        self.end_of_stage < now
    }
    /// returns the number of conflicts in the current stage
    pub fn current_span(&self) -> usize {
        self.cycle * self.unit_size
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
    /// returns a recommending number of redicible learnt clauses, based on
    /// the length of span.
    pub fn num_reducible(&self) -> usize {
        let span = self.current_span();
        let scale = (self.current_scale() as f64).sqrt();
        let keep = scale * self.unit_size as f64;
        span.saturating_sub(keep as usize)
    }
    /// returns the maximum factor so far.
    /// None: `luby_iter.max_value` holds the maximum value so far.
    /// This means it is the value found at the last segment.
    /// So the current value should be the next value, which is the double.
    pub fn max_scale(&self) -> usize {
        self.max_scale_of_segment
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
}

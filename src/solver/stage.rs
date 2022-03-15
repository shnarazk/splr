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
    scale: usize,
    end_of_stage: usize,
    next_is_new_segment: bool,
}

impl Instantiate for StageManager {
    fn instantiate(_: &Config, cnf: &CNFDescription) -> StageManager {
        let unit_size = (cnf.num_of_variables as f64).sqrt() as usize;
        StageManager {
            unit_size,
            scale: 1,
            end_of_stage: unit_size,
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
            scale: 1,
            end_of_stage: unit_size,
            next_is_new_segment: true,
        }
    }
    pub fn initialize(&mut self, unit_size: usize) {
        self.cycle = 0;
        self.unit_size = unit_size;
        self.scale = 1;
        self.end_of_stage = unit_size;
    }
    /// return:
    /// - Some(true): it's a beginning of a new cycle and a new 2nd-level cycle.
    /// - Some(false): a beginning of a new cycle.
    /// - None: the other case.
    pub fn prepare_new_stage(&mut self, rescale: usize, now: usize) -> Option<bool> {
        // self.scale *= 2;
        // self.stage += 1;
        // let span = self.current_span();
        // self.end_of_stage = now + span;
        // None
        self.unit_size = rescale;
        let mut new_cycle = false;
        let old_max = self.luby_iter.max_value();
        let old_scale = self.scale;
        self.scale = self.luby_iter.next_unchecked();
        if self.scale == 1 {
            self.cycle += 1;
            new_cycle = true;
            if self.next_is_new_segment {
                self.segment += 1;
                self.next_is_new_segment = false;
            }
        } else if old_max < self.scale {
            self.next_is_new_segment = true;
        }
        self.stage += 1;
        let span = self.current_span();
        self.end_of_stage = now + span;
        new_cycle.then(|| old_scale == self.luby_iter.max_value())
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
    pub fn num_reducible(&self) -> usize {
        const REDUCTION_FACTOR: f64 = 2.0;
        let span = self.current_span();
        let keep = (REDUCTION_FACTOR * (self.unit_size as f64).powf(0.75)) as usize;
        span.saturating_sub(keep)
    }
    /// return the maximum factor so far.
    pub fn max_scale(&self) -> usize {
        self.luby_iter.max_value()
    }
}

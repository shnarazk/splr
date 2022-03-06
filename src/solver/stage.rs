/// An implementation of CaDiCaL-style blocker.
/// I define it as a 'search mode', or stage, changer.
/// A stage is a span sharing same restart parameters.
/// And it also define the interval of clause reduction.
use {crate::types::*, splr_luby::LubySeries};

#[derive(Clone, Debug, Default)]
pub struct StageManager {
    cycle: usize,
    stage: usize,
    scale: usize,
    #[cfg(feature = "Luby_stabilization")]
    luby_iter: LubySeries,
    factor: usize,
    threshold: usize,
}

impl Instantiate for StageManager {
    fn instantiate(_: &Config, cnf: &CNFDescription) -> StageManager {
        let scale = (cnf.num_of_variables as f64).sqrt() as usize;
        StageManager {
            cycle: 1,
            scale,
            factor: 1,
            threshold: scale,
            ..StageManager::default()
        }
    }
    fn handle(&mut self, _: SolverEvent) {}
}

impl StageManager {
    pub fn new(scale: usize) -> Self {
        StageManager {
            cycle: 1,
            stage: 0,
            scale,
            #[cfg(feature = "Luby_stabilization")]
            luby_iter: LubySeries::default(),
            factor: 1,
            threshold: scale,
        }
    }
    pub fn initialize(&mut self, scale: usize) {
        self.cycle = 1;
        self.scale = scale;
        self.factor = 1;
        self.threshold = scale;
    }
    /// return:
    /// - Some(true): it's a beginning of a new cycle and a new 2nd-level cycle.
    /// - Some(false): a beginning of a new cycle.
    /// - None: the other case.
    pub fn prepare_new_stage(&mut self, rescale: usize, now: usize) -> Option<bool> {
        self.scale = rescale;
        #[cfg(feature = "Luby_stabilization")]
        {
            let mut new_cycle = false;
            let old_factor = self.factor;
            self.factor = self.luby_iter.next_unchecked();
            if self.factor == 1 {
                self.cycle += 1;
                new_cycle = true;
            }
            self.stage += 1;
            let span = self.current_span();
            self.threshold = now + span;
            new_cycle.then(|| old_factor == self.luby_iter.max_value())
        }
        #[cfg(not(feature = "Luby_stabilization"))]
        {
            self.factor *= 2;
            self.stage += 1;
            let span = self.current_span();
            self.threshold = now + span;
            None
        }
    }
    pub fn stage_ended(&self, now: usize) -> bool {
        self.threshold < now
    }
    /// return the number of conflicts in the current stage
    pub fn current_span(&self) -> usize {
        self.cycle * self.scale
    }
    pub fn num_reducible(&self) -> usize {
        // self.current_span() - self.scale / 2
        self.current_span() - 2 * (self.current_span() as f64).sqrt() as usize
        // self.current_span().saturating_sub(100)
    }
    pub fn current_stage(&self) -> usize {
        self.stage
    }
    pub fn current_cycle(&self) -> usize {
        self.cycle
    }
    /// return the factor of the current span
    pub fn current_scale(&self) -> usize {
        self.factor
    }
    /// return the maximum factor so far.
    #[cfg(feature = "Luby_stabilization")]
    pub fn max_scale(&self) -> usize {
        self.luby_iter.max_value()
    }
    #[cfg(not(feature = "Luby_stabilization"))]
    pub fn max_scale(&self) -> usize {
        self.factor
    }
}

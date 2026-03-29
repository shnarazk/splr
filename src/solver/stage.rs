/// An implementation of CaDiCaL-style blocker.
/// I define it as a 'search mode', or stage, changer.
/// A stage is a span sharing same restart parameters.
/// And it also define the interval of clause reduction.
use crate::types::*;

#[derive(Clone, Debug, Default)]
pub struct StageManager {
    luby_iter: LubySegment,
    end_of_span: usize,
    envelope_hight: usize,
    envelope_starting_segment: usize,
    next_is_new_envelope: bool,
}

impl StageManager {
    pub fn new() -> Self {
        StageManager {
            luby_iter: LubySegment::default(),
            envelope_hight: 1,
            end_of_span: 1,
            next_is_new_envelope: false,
            envelope_starting_segment: 1,
        }
    }
    pub fn initialize(&mut self) {
        self.envelope_hight = 1;
        self.end_of_span = 1;
        self.next_is_new_envelope = true;
    }
    pub fn reset(&mut self) {
        self.luby_iter.reset();
        self.envelope_hight = 1;
        self.end_of_span = 1;
        self.next_is_new_envelope = true;
    }
    /// returns:
    /// - Some(true): it's a beginning of a new envelope, a 2nd-level group.
    /// - Some(false): a beginning of a new segment.
    /// - None: the other case.
    pub fn prepare_new_span(&mut self, now: usize) -> Option<bool> {
        let mut new_segment = false;
        let mut new_envelope = false;
        self.luby_iter.shift();
        if self.luby_iter.segment_len() == 1 {
            self.envelope_starting_segment = self.luby_iter.seg_index as usize;
            new_segment = true;
            if self.next_is_new_envelope {
                self.envelope_hight += 1;
                self.next_is_new_envelope = false;
                new_envelope = true;
            }
        }
        if self.envelope_hight == self.luby_iter.segment_len() as usize {
            self.next_is_new_envelope = true;
        }
        self.end_of_span = now
            .checked_add(self.current_span())
            .expect("overflow at L57");
        new_segment.then_some(new_envelope)
    }
    pub fn span_ended(&self, now: usize) -> bool {
        self.end_of_span <= now
    }
    pub fn extend(&mut self, add: usize) {
        self.end_of_span += add;
    }
    /// returns the number of conflicts in the current stage
    /// Note: we need not to make a strong correlation between this value and
    /// scale defined by Luby series. So this is fine.
    pub fn current_span(&self) -> usize {
        self.luby_iter.luby() as usize
    }
    pub fn current_segment(&self) -> usize {
        self.luby_iter.seg_index as usize
    }
    pub fn envelop_index(&self) -> usize {
        self.envelope_hight
    }
    /// returns the scaling factor used in the current span
    pub fn current_segment_length(&self) -> usize {
        self.luby_iter.segment_len() as usize
    }
    /// returns the zero-based index in the current segment
    pub fn current_index_in_segment(&self) -> usize {
        self.luby_iter.ix_in_seg as usize
    }
    /// returns a recommending number of redicible learnt clauses, based on
    /// the length of span.
    pub fn num_reducible(&self, reducing_factor: f64) -> usize {
        let span = self.current_span();
        // let scale = (self.current_scale() as f64).powf(0.6);
        // let keep = scale * self.unit_size as f64;
        let keep = (span as f64).powf(1.0 - reducing_factor) as usize;
        span.saturating_sub(keep)
    }
    /// returns the maximum factor so far.
    /// None: `luby_iter.max_value` holds the maximum value so far.
    /// This means it is the value found at the last segment.
    /// So the current value should be the next value, which is the double.
    pub fn envelope_starting_segment(&self) -> usize {
        self.envelope_starting_segment
    }
}

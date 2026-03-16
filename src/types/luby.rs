//! O(1) Luby sequence implementation based on https://github.com/shnarazk/LubySequence
use std::{fmt, num::NonZeroU32};

#[derive(Clone, Debug)]
pub struct LubySegment {
    pub as_n: usize,
    pub seg_index: u32,
    pub ix_in_seg: u32,
}

impl Default for LubySegment {
    fn default() -> Self {
        LubySegment {
            as_n: 0,
            seg_index: 1,
            ix_in_seg: 0,
        }
    }
}

impl fmt::Display for LubySegment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Luby[n: {}, seg:{}, ix:{}]",
            self.as_n, self.seg_index, self.ix_in_seg
        )
    }
}

impl LubySegment {
    pub fn segment_len(&self) -> u32 {
        self.seg_index.trailing_zeros() + 1
    }
    pub fn luby(&self) -> u32 {
        2_u32.pow(self.ix_in_seg)
    }
    pub fn to_next(&self) -> Self {
        if self.ix_in_seg + 1 == self.segment_len() {
            Self {
                as_n: self.as_n + 1,
                seg_index: self.seg_index + 1,
                ix_in_seg: 0,
            }
        } else {
            Self {
                as_n: self.as_n + 1,
                seg_index: self.seg_index,
                ix_in_seg: self.ix_in_seg + 1,
            }
        }
    }
    pub fn shift(&mut self) -> &mut Self {
        self.as_n += 1;
        if self.ix_in_seg + 1 == self.segment_len() {
            self.seg_index += 1;
            self.ix_in_seg = 0;
        } else {
            self.ix_in_seg += 1;
        }
        self
    }
    pub fn reset(&mut self) {
        self.as_n = 0;
        self.seg_index = 1;
        self.ix_in_seg = 0;
    }
}

impl Iterator for LubySegment {
    type Item = Self;
    /// Find the finite subsequence that contains index 'x', and the
    /// size of that subsequence as: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8
    fn next(&mut self) -> Option<Self> {
        Some(self.to_next())
    }
}

#[derive(Clone, Debug)]
pub struct LubySeries {
    index: usize,
    seq: isize,
    size: usize,
    max_value: usize,
}

impl Default for LubySeries {
    fn default() -> Self {
        LubySeries {
            index: 0,
            seq: 0,
            size: 1,
            max_value: 1,
        }
    }
}

impl fmt::Display for LubySeries {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Luby[index:{}]", self.index)
    }
}

impl Iterator for LubySeries {
    type Item = NonZeroU32;
    /// Find the finite subsequence that contains index 'x', and the
    /// size of that subsequence as: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8
    fn next(&mut self) -> Option<NonZeroU32> {
        self.index += 1;
        let mut seq = self.seq;
        let mut size = self.size;
        while size < self.index + 1 {
            self.seq = seq;
            seq += 1;
            self.size = size;
            size = 2 * size + 1;
        }
        let mut index = self.index;
        while size - 1 != index {
            size = (size - 1) >> 1;
            seq -= 1;
            index %= size;
        }
        let val = 2usize.pow(seq as u32);
        if self.max_value < val {
            self.max_value = val;
        }
        NonZeroU32::new(val as u32)
    }
}

impl LubySeries {
    pub fn next_unchecked(&mut self) -> usize {
        self.index += 1;
        let mut seq = self.seq;
        let mut size = self.size;
        while size < self.index + 1 {
            self.seq = seq;
            seq += 1;
            self.size = size;
            size = 2 * size + 1;
        }
        let mut index = self.index;
        while size - 1 != index {
            size = (size - 1) >> 1;
            seq -= 1;
            index %= size;
        }
        let val = 2usize.pow(seq as u32);
        if self.max_value < val {
            self.max_value = val;
        }
        val
    }
    pub fn max_value(&self) -> usize {
        self.max_value
    }
    pub fn reset(&mut self) {
        self.index = 0;
        self.seq = 0;
        self.size = 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_luby_series() {
        let mut luby = LubySeries::default();
        // Note: Luby sequence starts with 1, 1, 2, ...
        // We can't take the first value in the following iteration.
        let v = vec![1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        let l = v
            .iter()
            .map(|_| luby.next_unchecked())
            .collect::<Vec<usize>>();
        assert_eq!(l, v);
    }
    #[test]
    fn test_luby_segment1() {
        let mut luby = LubySegment::default();
        assert_eq!(luby.seg_index, 1);
        assert_eq!(luby.ix_in_seg, 0);
        assert_eq!(luby.luby(), 1);
        luby.shift();
        assert_eq!(luby.seg_index, 2);
        assert_eq!(luby.ix_in_seg, 0);
        assert_eq!(luby.luby(), 1);
    }
    #[test]
    fn test_luby_segment2() {
        let mut luby = LubySegment::default();
        let v = vec![1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        let l = v
            .iter()
            .map(|_| luby.shift().luby() as usize)
            .collect::<Vec<usize>>();
        assert_eq!(l, v);
    }
}

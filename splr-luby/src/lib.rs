use std::{fmt, num::NonZeroU32};

#[derive(Clone, Debug)]
pub struct LubySeries {
    index: usize,
    seq: isize,
    size: usize,
}

impl Default for LubySeries {
    fn default() -> Self {
        LubySeries {
            index: 0,
            seq: 0,
            size: 1,
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
        NonZeroU32::new(2usize.pow(seq as u32) as u32)
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
        2usize.pow(seq as u32)
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
    fn test_progress_luby() {
        let mut luby = ProgressLuby {
            enable: true,
            active: true,
            step: 1,
            next_restart: 1,
            ..ProgressLuby::default()
        };
        luby.update(0);
        for v in vec![
            1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1,
        ] {
            assert_eq!(luby.next_restart, v);
            luby.shift();
        }
    }
    #[test]
    fn test_luby_series() {
        let mut luby = LubySeries::default();
        let v = vec![1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        let mut l: Vec<usize> = vec![];
        for _ in 1..15 {
            l.push(luby.next());
        }
        assert_eq!(l, v);
    }
}

use {
    super::ClauseId,
    crate::types::*,
    std::ops::{Index, IndexMut},
};

pub struct ClauseIdVector(Vec<ClauseId>);

pub trait ClauseIdVectorIF {
    fn get(&self, i: usize) -> Option<ClauseId>;
    fn remove_cid(&mut self, cid: ClauseId);
    fn insert_cid(&mut self, cid: ClauseId);
}

impl ClauseIdVectorIF for ClauseIdVector {
    fn get(&self, i: usize) -> Option<ClauseId> {
        self.0.get(i).copied()
    }
    fn remove_cid(&mut self, cid: ClauseId) {
        if let Some(i) = self.0.iter().position(|e| *e == cid) {
            self.0.swap_remove(i);
        }
    }
    fn insert_cid(&mut self, cid: ClauseId) {
        self.0.push(cid);
    }
}

impl Index<Lit> for Vec<ClauseIdVector> {
    type Output = ClauseIdVector;
    #[inline]
    fn index(&self, l: Lit) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self[usize::from(l)]
    }
}

impl IndexMut<Lit> for Vec<ClauseIdVector> {
    #[inline]
    fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked_mut(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self[usize::from(l)]
    }
}

pub struct ClauseIdIterator {
    pub index: usize,
    end_at: usize,
    // checksum: usize,
}

impl Iterator for ClauseIdIterator {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        // assert!(self.checksum == self.end_at - self.index);
        (self.index < self.end_at).then_some({
            // assert!(0 < self.checksum);
            // self.checksum -= 1;
            self.index
        })
    }
}

impl ClauseIdIterator {
    pub fn new(len: usize) -> Self {
        ClauseIdIterator {
            index: 0,
            end_at: len,
            // checksum: len,
        }
    }
    pub fn restore_entry(&mut self) {
        self.index += 1;
    }
    pub fn detach_entry(&mut self) {
        // assert!(self.end_at != 0);
        self.end_at -= 1;
    }
}

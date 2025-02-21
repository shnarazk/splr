use {
    super::ClauseId,
    crate::types::*,
    std::{
        //        collections::HashMap,
        ops::{Index, IndexMut},
    },
};

pub type WatchCacheList = Vec<(ClauseId, Lit)>;
pub type WatchCache = WatchCacheList;

pub trait WatchCacheIF {
    fn get_watch(&self, cid: &ClauseId) -> Option<&Lit>;
    fn remove_watch(&mut self, cid: &ClauseId);
    fn insert_watch(&mut self, cid: ClauseId, l: Lit);
    fn append_watch(&mut self, appendant: Self);
    fn update_watch(&mut self, cid: ClauseId, l: Lit);
}

impl WatchCacheIF for WatchCacheList {
    fn get_watch(&self, cid: &ClauseId) -> Option<&Lit> {
        self.iter().find_map(|e| (e.0 == *cid).then_some(&e.1))
    }
    fn remove_watch(&mut self, cid: &ClauseId) {
        if let Some(i) = self.iter().position(|e| e.0 == *cid) {
            self.swap_remove(i);
        }
    }
    fn insert_watch(&mut self, cid: ClauseId, l: Lit) {
        debug_assert!(self.iter().all(|e| e.0 != cid));
        self.push((cid, l));
    }
    fn append_watch(&mut self, mut appendant: Self) {
        self.append(&mut appendant);
    }
    fn update_watch(&mut self, cid: ClauseId, l: Lit) {
        for e in self.iter_mut() {
            if e.0 == cid {
                e.1 = l;
                break;
            }
        }
    }
}

// impl Index<Lit> for Vec<HashMap<Lit, ClauseId>> {
//     type Output = HashMap<Lit, ClauseId>;
//     #[inline]
//     fn index(&self, l: Lit) -> &Self::Output {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.get_unchecked(usize::from(l))
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self[usize::from(l)]
//     }
// }

// impl IndexMut<Lit> for Vec<HashMap<Lit, ClauseId>> {
//     #[inline]
//     fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.get_unchecked_mut(usize::from(l))
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self[usize::from(l)]
//     }
// }

impl Index<Lit> for Vec<WatchCache> {
    type Output = WatchCache;
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

impl IndexMut<Lit> for Vec<WatchCache> {
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

pub type WatchCacheProxy = usize;

pub struct WatchCacheIterator {
    pub index: usize,
    end_at: usize,
    // checksum: usize,
}

impl Iterator for WatchCacheIterator {
    type Item = WatchCacheProxy;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // assert!(self.checksum == self.end_at - self.index);
        (self.index < self.end_at).then_some({
            // assert!(0 < self.checksum);
            // self.checksum -= 1;
            self.index
        })
    }
}

impl WatchCacheIterator {
    pub fn new(len: usize) -> Self {
        WatchCacheIterator {
            index: 0,
            end_at: len,
            // checksum: len,
        }
    }
    #[inline]
    pub fn restore_entry(&mut self) {
        self.index += 1;
    }
    #[inline]
    pub fn detach_entry(&mut self) {
        // assert!(self.end_at != 0);
        self.end_at -= 1;
    }
}

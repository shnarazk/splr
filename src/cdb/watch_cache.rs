use {
    super::ClauseId,
    crate::types::*,
    std::{
        collections::HashMap,
        ops::{Index, IndexMut},
    },
};

pub type WatchCacheList<'a> = Vec<(ClauseId, Lit<'a>)>;
pub type WatchCache<'a> = WatchCacheList<'a>;

pub trait WatchCacheIF<'a> {
    fn get_watch(&'a self, cid: &'a ClauseId) -> Option<&'a Lit<'a>>;
    fn remove_watch(&mut self, cid: &ClauseId);
    fn insert_watch(&mut self, cid: ClauseId, l: Lit<'a>);
    fn append_watch(&mut self, appendant: Self);
    fn update_watch(&mut self, cid: ClauseId, l: Lit<'a>);
}

impl<'a> WatchCacheIF<'a> for WatchCacheList<'a> {
    fn get_watch(&'a self, cid: &'a ClauseId) -> Option<&'a Lit<'a>> {
        self.iter().find_map(|e| (e.0 == *cid).then_some(&e.1))
    }
    fn remove_watch(&mut self, cid: &ClauseId) {
        if let Some(i) = self.iter().position(|e| e.0 == *cid) {
            self.swap_remove(i);
        }
    }
    fn insert_watch(&mut self, cid: ClauseId, l: Lit<'a>) {
        debug_assert!(self.iter().all(|e| e.0 != cid));
        self.push((cid, l));
    }
    fn append_watch(&mut self, mut appendant: Self) {
        self.append(&mut appendant);
    }
    fn update_watch(&mut self, cid: ClauseId, l: Lit<'a>) {
        for e in self.iter_mut() {
            if e.0 == cid {
                e.1 = l;
                break;
            }
        }
    }
}

impl<'a> Index<Lit<'a>> for Vec<HashMap<Lit<'a>, ClauseId>> {
    type Output = HashMap<Lit<'a>, ClauseId>;
    #[inline]
    fn index(&self, l: Lit<'a>) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self[usize::from(l)]
    }
}

impl<'a> IndexMut<Lit<'a>> for Vec<HashMap<Lit<'a>, ClauseId>> {
    #[inline]
    fn index_mut(&mut self, l: Lit<'a>) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked_mut(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self[usize::from(l)]
    }
}

impl<'a> Index<Lit<'a>> for Vec<WatchCache<'a>> {
    type Output = WatchCache<'a>;
    #[inline]
    fn index(&self, l: Lit<'a>) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked(usize::from(l))
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self[usize::from(l)]
    }
}

impl<'a> IndexMut<Lit<'a>> for Vec<WatchCache<'a>> {
    #[inline]
    fn index_mut(&mut self, l: Lit<'a>) -> &mut Self::Output {
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
    pub fn restore_entry(&mut self) {
        self.index += 1;
    }
    pub fn detach_entry(&mut self) {
        // assert!(self.end_at != 0);
        self.end_at -= 1;
    }
}

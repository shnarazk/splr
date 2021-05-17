use {
    super::ClauseId,
    crate::types::*,
    std::{
        collections::HashMap,
        ops::{Index, IndexMut},
    },
};

pub type BiClause = HashMap<Lit, ClauseId>;
pub type WatchCacheHash = HashMap<ClauseId, Lit>;
pub type WatchCacheList = Vec<(ClauseId, Lit)>;

#[cfg(feature = "hashed_watch_cache")]
pub type WatchCache = WatchCacheHash;
#[cfg(not(feature = "hashed_watch_cache"))]
pub type WatchCache = WatchCacheList;

pub trait WatchCacheIF {
    fn get_watch(&self, cid: &ClauseId) -> Option<&Lit>;
    fn remove_watch(&mut self, cid: &ClauseId) -> Option<Lit>;
    fn insert_watch(&mut self, cid: ClauseId, l: Lit);
    fn insert_or_update_watch(&mut self, cid: ClauseId, l: Lit);
    fn append_watch(&mut self, appendant: Self);
}

impl WatchCacheIF for WatchCacheHash {
    fn get_watch(&self, cid: &ClauseId) -> Option<&Lit> {
        self.get(cid)
    }
    fn remove_watch(&mut self, cid: &ClauseId) -> Option<Lit> {
        self.remove(cid)
    }
    fn insert_watch(&mut self, cid: ClauseId, l: Lit) {
        self.insert(cid, l);
    }
    fn insert_or_update_watch(&mut self, cid: ClauseId, l: Lit) {
        self.insert(cid, l);
    }
    fn append_watch(&mut self, appendant: Self) {
        for (k, v) in appendant.iter() {
            self.insert(*k, *v);
        }
    }
}

impl WatchCacheIF for WatchCacheList {
    fn get_watch(&self, cid: &ClauseId) -> Option<&Lit> {
        for e in self.iter() {
            if e.0 == *cid {
                return Some(&e.1);
            }
        }
        None
    }
    fn remove_watch(&mut self, cid: &ClauseId) -> Option<Lit> {
        for (i, e) in self.iter().enumerate() {
            if e.0 == *cid {
                let tmp = e.1;
                self.swap_remove(i);
                return Some(tmp);
            }
        }
        None
    }
    fn insert_watch(&mut self, cid: ClauseId, l: Lit) {
        debug_assert!(self.iter().all(|e| e.0 != cid));
        self.push((cid, l));
    }
    fn insert_or_update_watch(&mut self, cid: ClauseId, l: Lit) {
        for e in self.iter_mut() {
            if e.0 == cid {
                e.1 = l;
                return;
            }
        }
        self.push((cid, l));
    }
    fn append_watch(&mut self, mut appendant: Self) {
        self.append(&mut appendant);
    }
}

impl Index<Lit> for Vec<HashMap<Lit, ClauseId>> {
    type Output = HashMap<Lit, ClauseId>;
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

impl IndexMut<Lit> for Vec<HashMap<Lit, ClauseId>> {
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

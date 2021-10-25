use {
    super::ClauseId,
    crate::types::*,
    std::{
        collections::HashMap,
        ops::{Index, IndexMut},
    },
};

pub type BiClause = HashMap<Lit, ClauseId>;
pub type BinaryLinkList = Vec<(Lit, ClauseId)>;

impl Index<Lit> for Vec<BinaryLinkList> {
    type Output = BinaryLinkList;
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

impl IndexMut<Lit> for Vec<BinaryLinkList> {
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

#[derive(Clone, Debug)]
pub struct BinaryLinkDB {
    hash: Vec<BiClause>,
    list: Vec<BinaryLinkList>,
}

pub trait BinaryLinkIF {
    fn add(&mut self, lit0: Lit, lit1: Lit, cid: ClauseId);
    fn remove(&mut self, lit0: Lit, lit1: Lit) -> MaybeInconsistent;
    fn search(&self, lit0: Lit, lit1: Lit) -> Option<ClauseId>;
    fn watch_cache_of(&self, lit: Lit) -> &BinaryLinkList;
}

impl BinaryLinkIF for BinaryLinkDB {
    fn add(&mut self, lit0: Lit, lit1: Lit, cid: ClauseId) {
        self.hash[lit0].insert(lit1, cid);
        self.list[lit0].push((lit1, cid));
        self.hash[lit1].insert(lit0, cid);
        self.list[lit1].push((lit0, cid));
    }
    fn remove(&mut self, lit0: Lit, lit1: Lit) -> MaybeInconsistent {
        self.hash[lit0].remove(&lit1);
        self.list[lit0].delete_unstable(|p| p.0 == lit1);
        self.hash[lit1].remove(&lit0);
        self.list[lit1].delete_unstable(|p| p.0 == lit0);
        Ok(())
    }
    fn search(&self, lit0: Lit, lit1: Lit) -> Option<ClauseId> {
        self.hash[lit0].get(&lit1).copied()
    }
    fn watch_cache_of(&self, lit: Lit) -> &BinaryLinkList {
        &self.list[lit]
    }
}

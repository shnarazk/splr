use {
    super::ClauseId,
    crate::{solver::SolverEvent, types::*},
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

impl Instantiate for BinaryLinkDB {
    fn instantiate(_conf: &Config, cnf: &CNFDescription) -> Self {
        let num_lit = 2 * cnf.num_of_variables + 1;
        BinaryLinkDB {
            hash: vec![HashMap::new(); num_lit],
            list: vec![Vec::new(); num_lit],
        }
    }
    fn handle(&mut self, _e: SolverEvent) {}
}

pub trait BinaryLinkIF {
    /// add a mapping from a pair of Lit to a `ClauseId`
    fn add(&mut self, lit0: Lit, lit1: Lit, cid: ClauseId);
    /// remove a pair of `Lit`s
    fn remove(&mut self, lit0: Lit, lit1: Lit) -> MaybeInconsistent;
    /// return 'ClauseId` linked from a pair of `Lit`s
    fn search(&self, lit0: Lit, lit1: Lit) -> Option<ClauseId>;
    /// return the watch_cache for a `Lit`
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

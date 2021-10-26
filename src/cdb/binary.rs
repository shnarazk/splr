use {
    super::ClauseId,
    crate::{solver::SolverEvent, types::*},
    std::{
        collections::HashMap,
        ops::{Index, IndexMut},
    },
};

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
    hash: HashMap<(Lit, Lit), ClauseId>,
    list: Vec<BinaryLinkList>,
}

impl Default for BinaryLinkDB {
    fn default() -> Self {
        BinaryLinkDB {
            hash: HashMap::new(),
            list: Vec::new(),
        }
    }
}

impl Instantiate for BinaryLinkDB {
    fn instantiate(_conf: &Config, cnf: &CNFDescription) -> Self {
        let num_lit = 2 * (cnf.num_of_variables + 1);
        BinaryLinkDB {
            hash: HashMap::new(),
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
    /// return the all links that include `Lit`.
    /// Note this is not a `watch_list`. The other literal has an opposite phase.
    fn connect_with(&self, lit: Lit) -> &BinaryLinkList;
    /// add new var
    fn add_new_var(&mut self);
}

impl BinaryLinkIF for BinaryLinkDB {
    fn add(&mut self, lit0: Lit, lit1: Lit, cid: ClauseId) {
        let l0 = lit0.min(lit1);
        let l1 = lit0.max(lit1);
        self.hash.insert((l0, l1), cid);
        self.list[lit0].push((lit1, cid));
        self.list[lit1].push((lit0, cid));
    }
    fn remove(&mut self, lit0: Lit, lit1: Lit) -> MaybeInconsistent {
        let l0 = lit0.min(lit1);
        let l1 = lit0.max(lit1);
        self.hash.remove(&(l0, l1));
        self.list[lit0].delete_unstable(|p| p.0 == lit1);
        self.list[lit1].delete_unstable(|p| p.0 == lit0);
        Ok(())
    }
    fn search(&self, lit0: Lit, lit1: Lit) -> Option<ClauseId> {
        let l0 = lit0.min(lit1);
        let l1 = lit0.max(lit1);
        self.hash.get(&(l0, l1)).copied()
    }
    fn connect_with(&self, lit: Lit) -> &BinaryLinkList {
        &self.list[lit]
    }
    fn add_new_var(&mut self) {
        for _ in 0..2 {
            self.list.push(Vec::new());
        }
    }
}

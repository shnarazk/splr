use {
    crate::types::*,
    std::{
        collections::hash_map::HashMap,
        ops::{Index, IndexMut},
        slice::Iter,
    },
};

/// storage of binary links
pub type BinaryLinkList = Vec<(Lit, ClauseIndex)>;

impl Index<Lit> for Vec<BinaryLinkList> {
    type Output = BinaryLinkList;
    fn index(&self, l: Lit) -> &Self::Output {
        &self[usize::from(l)]
    }
}

impl IndexMut<Lit> for Vec<BinaryLinkList> {
    fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
        &mut self[usize::from(l)]
    }
}

/// storage with mapper to `ClauseIndex` of binary links
#[derive(Clone, Debug, Default)]
pub struct BinaryLinkDB {
    pub(super) hash: HashMap<Lit, BinaryLinkList>,
    empty: BinaryLinkList,
}

impl Instantiate for BinaryLinkDB {
    fn instantiate(_conf: &Config, _cnf: &CNFDescription) -> Self {
        BinaryLinkDB {
            hash: HashMap::new(),
            empty: BinaryLinkList::default(),
        }
    }
    fn handle(&mut self, _e: SolverEvent) {}
}

pub trait BinaryLinkIF {
    /// add a mapping from a pair of Lit to a `ClauseIndex`
    fn add(&mut self, lit0: Lit, lit1: Lit, cid: ClauseIndex);
    /// remove a pair of `Lit`s
    fn remove(&mut self, lit0: Lit, lit1: Lit) -> MaybeInconsistent;
    /// return 'ClauseIndex` linked from a pair of `Lit`s
    fn search(&self, lit0: Lit, lit1: Lit) -> Option<ClauseIndex>;
    /// add new var
    fn add_new_var(&mut self);
    /// iterate on binary clauses containing `lit`
    fn iter(&self, lit: Lit) -> Iter<(Lit, ClauseIndex)>;
}

impl BinaryLinkIF for BinaryLinkDB {
    fn add(&mut self, lit0: Lit, lit1: Lit, cid: ClauseIndex) {
        self.hash.entry(lit0).or_default().push((lit1, cid));
        self.hash.entry(lit1).or_default().push((lit0, cid));
    }
    /// O(n)
    fn remove(&mut self, lit0: Lit, lit1: Lit) -> MaybeInconsistent {
        self.hash
            .entry(lit0)
            .and_modify(|l| l.delete_unstable(|lc| lc.0 == lit1));
        self.hash
            .entry(lit1)
            .and_modify(|l| l.delete_unstable(|lc| lc.0 == lit0));
        Ok(())
    }
    fn search(&self, lit0: Lit, lit1: Lit) -> Option<ClauseIndex> {
        self.hash
            .get(&lit0)
            .and_then(|v| v.iter().find(|e| e.0 == lit1))
            .map(|e| e.1)
    }
    fn add_new_var(&mut self) {}
    fn iter(&self, lit: Lit) -> Iter<(Lit, ClauseIndex)> {
        self.hash.get(&lit).unwrap_or(&self.empty).iter()
    }
}

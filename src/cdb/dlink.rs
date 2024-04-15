use {
    crate::{cdb::clause::*, types::*},
    std::ops::{Index, IndexMut},
};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DoubleLink {
    pub prev: ClauseIndex,
    pub next: ClauseIndex,
}

pub trait DancingIndexIF {
    type Element;
    fn next_for_lit(clause: &Self::Element, lit: Lit) -> ClauseIndex;
    fn next_for_lit_mut(clause: &mut Self::Element, lit: Lit) -> &mut ClauseIndex;
    fn prev_for_lit(clause: &Self::Element, lit: Lit) -> ClauseIndex;
    fn prev_for_lit_mut(clause: &mut Self::Element, lit: Lit) -> &mut ClauseIndex;
    // fn erase_links(clause: &mut Self::Element);
    fn get_watcher_link(&mut self, lit: Lit) -> ClauseIndex;
    fn get_free_watcher(&mut self) -> ClauseIndex;
    fn insert_watcher(&mut self, lit: Lit, index: ClauseIndex);
    fn remove_watcher(&mut self, lit: Lit, index: ClauseIndex);
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinkHead {
    pub prev: ClauseIndex,
    pub next: ClauseIndex,
    pub count: ClauseIndex,
    pub timestamp: ClauseIndex,
}

struct ClauseDB {
    pub header: Vec<LinkHead>,
    pub clause: Vec<Clause>,
}

impl Index<Lit> for ClauseDB {
    type Output = Clause;
    #[inline]
    fn index(&self, lit: Lit) -> &Self::Output {
        &self.clause[ClauseIndex::from(lit)]
    }
}

impl IndexMut<Lit> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, lit: Lit) -> &mut Self::Output {
        &mut self.clause[ClauseIndex::from(lit)]
    }
}

impl Instantiate for ClauseDB {
    fn instantiate(conf: &Config, cnf: &CNFDescription) -> Self {
        unimplemented!()
    }
}

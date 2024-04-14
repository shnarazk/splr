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
    fn prev_for_lit_mut(clause: &Self::Element, lit: Lit) -> &mut ClauseIndex;
    fn erase_links(clause: &mut Self::Element);
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

pub struct ClauseDB {
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

const HEAD_INDEX: ClauseIndex = 0;
const FREE_INDEX: ClauseIndex = 1;

impl DancingIndexHeaderIF for ClauseDB {
    fn get_watcher_link(&mut self, lit: Lit) -> ClauseIndex {
        self.clause[ClauseIndex::from(lit)].next_for_lit(lit)
    }
    fn get_free_watcher(&mut self) -> ClauseIndex {
        let index = self.header[FREE_INDEX].next;
        if index != 0 {
            let next = self.clause[FREE_INDEX].link0.next;
            self.header[FREE_INDEX].next = next;
            self.clause[index].erase_links();
            index
        } else {
            self.clause.push(Clause::default());
            1 + self.clause.len()
        }
    }
    fn insert_watcher(&mut self, lit: Lit, index: ClauseIndex) {
        let last = self.header[ClauseIndex::from(lit)].prev;
        *self.clause[last].next_for_lit_mut(lit) = index;
        *self.clause[index].prev_for_lit_mut(lit) = last;
        *self.clause[index].next_for_lit_mut(lit) = HEAD_INDEX;
        self.header[ClauseIndex::from(lit)].prev = index;
    }
    fn remove_watcher(&mut self, lit: Lit, index: ClauseIndex) {
        let next = self.clause[ClauseIndex::from(lit)].next_for_lit(lit);
        let prev = self.clause[ClauseIndex::from(lit)].prev_for_lit(lit);
        *self.clause[prev].next_for_lit_mut(lit) = next;
        *self.clause[next].prev_for_lit_mut(lit) = prev;
        let p = self.header[FREE_INDEX].prev;
        self.clause[p].link0.next = index;
        self.clause[index].link0.prev = p;
        self.clause[index].link0.next = HEAD_INDEX;
    }
}

impl Instantiate for ClauseDB {
    fn instantiate(conf: &Config, cnf: &CNFDescription) -> Self {
        unimplemented!()
    }
}

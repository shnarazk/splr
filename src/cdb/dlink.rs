use {
    crate::types::*,
    std::ops::{Index, IndexMut},
};

type ClauseIndex = usize;

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DoubleLink {
    pub prev: ClauseIndex,
    pub next: ClauseIndex,
}

pub struct Clause {
    pub link0: DoubleLink,
    pub link1: DoubleLink,
    pub lits: Vec<Lit>,
}

impl Clause {
    fn next_for_lit(&self, lit: Lit) -> ClauseIndex {
        if self.lits[0] == lit {
            self.link0.next;
        }
        if self.lits[1] == lit {
            self.link1.next;
        }
        panic!("ilegal chain")
    }
    fn next_for_lit_mut(&mut self, lit: Lit) -> &mut ClauseIndex {
        if self.lits[0] == lit {
            &mut self.link0.next;
        }
        if self.lits[1] == lit {
            &mut self.link1.next;
        }
        panic!("ilegal chain")
    }
    fn prev_for_lit(&self, lit: Lit) -> ClauseIndex {
        if self.lits[0] == lit {
            self.link0.prev;
        }
        if self.lits[1] == lit {
            self.link1.prev;
        }
        panic!("ilegal chain")
    }
    fn prev_for_lit_mut(&self, lit: Lit) -> &mut ClauseIndex {
        if self.lits[0] == lit {
            &mut self.link0.prev;
        }
        if self.lits[1] == lit {
            &mut self.link1.prev;
        }
        panic!("ilegal chain")
    }
    fn erase_links(&mut self) {
        self.link0.prev = 0;
        self.link0.next = 0;
        self.link1.prev = 0;
        self.link1.next = 0;
    }
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

pub trait DancingIndexIF {
    fn get_watcher_link(&mut self, lit: Lit) -> ClauseIndex;
    fn get_free_watcher(&mut self) -> ClauseIndex;
    fn insert_watcher(&mut self, lit: Lit, index: ClauseIndex);
    fn remove_watcher(&mut self, lit: Lit, index: ClauseIndex);
}

const HEAD_INDEX: ClauseIndex = 0;
const FREE_INDEX: ClauseIndex = 1;

impl DancingIndexIF for ClauseDB {
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

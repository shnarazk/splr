use {
    crate::types::*,
    std::ops::{Index, IndexMut},
};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DoubleLink {
    pub prev: usize,
    pub next: usize,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinkHead {
    pub prev: usize,
    pub next: usize,
    pub count: usize,
    pub timestamp: usize,
}

pub struct DancingLinks {
    pub watch: Vec<LinkHead>,
}

impl Index<Lit> for DancingLinks {
    type Output = LinkHead;
    #[inline]
    fn index(&self, lit: Lit) -> &Self::Output {
        &self.watch[usize::from(lit)]
    }
}

impl IndexMut<Lit> for DancingLinks {
    #[inline]
    fn index_mut(&mut self, lit: Lit) -> &mut Self::Output {
        &mut self.watch[usize::from(lit)]
    }
}

pub trait DancingLinkIF {
    type Element;
    fn next_watcher(&mut self, lit: Lit) -> usize;
    fn prev_watcher(&mut self, lit: Lit) -> usize;
    fn insert(&mut self, index: usize);
    fn free_element(&mut self) -> Option<usize>;
}

impl DancingLinkIF for DancingLinks {
    type Element = Clause;
    fn next_watcher(&mut self, lit: Lit) -> usize {
        self[lit].next
    }
    fn prev_watcher(&mut self, lit: Lit) -> usize {
        return 0;
    }
    fn insert(&mut self, index: usize) {}
    fn free_element(&mut self) -> Option<usize> {
        return None;
    }
}

impl Instantiate for DancingLinks {
    fn instantiate(conf: &Config, cnf: &CNFDescription) -> Self {
        unimplemented!()
    }
}

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
    pub element: Vec<DoubleLink>,
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
    fn insert_watcher(&mut self, lit: Lit, index: usize);
    fn remove_watcher(&mut self, lit: Lit, index: usize);
    fn get_free_watcher(&mut self) -> Option<usize>;
}

impl DancingLinkIF for DancingLinks {
    type Element = Clause;
    fn next_watcher(&mut self, lit: Lit) -> usize {
        self.watch[usize::from(lit)].next
    }
    fn prev_watcher(&mut self, lit: Lit) -> usize {
        self.watch[usize::from(lit)].prev
    }
    fn insert_watcher(&mut self, lit: Lit, index: usize) {
        let prev = self.watch[usize::from(lit)].prev;
        self.element[prev].next = index;
        self.element[index].prev = prev;
        self.element[index].next = 0;
        self.watch[usize::from(lit)].next = index;
    }
    fn remove_watcher(&mut self, lit: Lit, index: usize) {
        let next = self.watch[usize::from(lit)].next;
        let prev = self.watch[usize::from(lit)].prev;
        self.element[prev].next = next;
        self.element[next].prev = prev;
        let p = self.element[1].prev;
        self.element[p].next = index;
        self.element[index].prev = p;
        self.element[index].next = 0;
    }
    fn get_free_watcher(&mut self) -> Option<usize> {
        let index = self.watch[1].next;
        (index != 0).then_some(index)
    }
}

impl Instantiate for DancingLinks {
    fn instantiate(conf: &Config, cnf: &CNFDescription) -> Self {
        unimplemented!()
    }
}

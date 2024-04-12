use crate::types::*;

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

pub trait DancingLinkIF {
    type Element;
    fn next_watcher(&mut self, lit: Lit) -> usize;
    fn prev_watcher(&mut self, lit: Lit) -> usize;
    fn insert(&mut self, index: usize);
    fn free_element(&mut self) -> Option<usize>;
}

impl Instantiate for DancingLinks {
    fn instantiate(conf: &Config, cnf: &CNFDescription) -> Self {
        unimplemented!()
    }
}

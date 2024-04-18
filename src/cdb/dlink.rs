use crate::types::*;

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DoubleLink {
    pub prev: ClauseIndex,
    pub next: ClauseIndex,
}

pub trait DancingIndexIF {
    fn next_for_lit(&self, lit: Lit) -> ClauseIndex;
    fn next_for_lit_mut(&mut self, lit: Lit) -> &mut ClauseIndex;
    fn prev_for_lit(&self, lit: Lit) -> ClauseIndex;
    fn prev_for_lit_mut(&mut self, lit: Lit) -> &mut ClauseIndex;
    fn clear_links(&mut self);
}

pub trait DancingIndexManagerIF {
    fn get_watcher_link(&mut self, lit: Lit) -> ClauseIndex;
    fn get_free_index(&mut self) -> ClauseIndex;
    fn insert_watcher(&mut self, lit: Lit, index: ClauseIndex);
    fn remove_watcher(&mut self, lit: Lit, index: ClauseIndex);
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<LinkHead>;
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinkHead {
    pub prev: ClauseIndex,
    pub next: ClauseIndex,
    pub count: ClauseIndex,
    pub timestamp: ClauseIndex,
}

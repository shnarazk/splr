use crate::types::*;

// #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
// pub struct DoubleLink {
//     pub next: ClauseIndex,
// }

pub trait WatcherLinkIF {
    fn next_for_lit(&self, lit: Lit) -> ClauseIndex;
    fn next_for_lit_mut(&mut self, lit: Lit) -> &mut ClauseIndex;
    fn swap_watch_orders(&mut self);
}

pub trait ClauseWeaverIF {
    fn get_watcher_link(&mut self, lit: Lit) -> ClauseIndex;
    fn get_free_index(&mut self) -> ClauseIndex;
    fn insert_watcher(&mut self, ci: ClauseIndex, socond: bool, lit: Lit);
    fn remove_next_watcher(&mut self, ci: ClauseIndex, lit: Lit) -> bool;
    fn remove_watcher(&mut self, ci: ClauseIndex);
    fn mark_as_free(&mut self, index: ClauseIndex);
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<ClauseIndex>;
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinkHead {
    pub next: ClauseIndex,
    pub count: ClauseIndex,
    pub timestamp: ClauseIndex,
}

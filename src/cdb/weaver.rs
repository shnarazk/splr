use {
    crate::types::*,
    std::ops::{Index, IndexMut},
};

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct WatchLiteralIndexRef {
    pub(crate) prev: WatchLiteralIndex,
    pub(crate) next: WatchLiteralIndex,
}

impl WatchLiteralIndexRef {
    pub fn set(&mut self, prev: WatchLiteralIndex, next: WatchLiteralIndex) -> &mut Self {
        self.prev = prev;
        self.next = next;
        self
    }
}

impl Index<Lit> for [WatchLiteralIndexRef] {
    type Output = WatchLiteralIndexRef;
    fn index(&self, l: Lit) -> &Self::Output {
        &self[usize::from(l)]
    }
}

impl IndexMut<Lit> for [WatchLiteralIndexRef] {
    fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
        &mut self[usize::from(l)]
    }
}

pub trait WatcherLinkIF {
    fn next_watch(&self, wi: usize) -> WatchLiteralIndex;
    fn next_watch_mut(&mut self, wi: usize) -> &mut WatchLiteralIndex;
    fn prev_watch(&self, wi: usize) -> WatchLiteralIndex;
    fn prev_watch_mut(&mut self, wi: usize) -> &mut WatchLiteralIndex;
}

/// Note: this interface is based on ClauseIndex and Watch literal's position
/// in a clause.
pub trait ClauseWeaverIF {
    /// overwrite both link pairs for the present watch literals
    fn weave(&mut self, ci: ClauseIndex);
    /// separete from a *single* link pair for `wi`,
    /// swap `wi`-th lit and `wj`-th lit,
    /// then link to watcher list for the new watch leteral at `wi`
    fn reweave(&mut self, ci: ClauseIndex, wi: usize, wj: usize);
    /// separete from a *single link pair for `wi`
    fn unweave(&mut self, ci: ClauseIndex, wi: usize);
    /// instantiate a list of watch lists
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<WatchLiteralIndexRef>;
    /// return the first watch literal index for literal `lit`
    fn get_first_watch(&mut self, lit: Lit) -> WatchLiteralIndex;
    /// return a ClauseIndex of an unused clause
    fn get_free_index(&mut self) -> ClauseIndex;
}

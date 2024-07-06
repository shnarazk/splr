use crate::types::*;

#[derive(Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct WatchLiteralIndexRef {
    prev: WatchLiteralIndex,
    next: WatchLiteralIndex,
}

pub trait WatcherLinkIF {
    fn next_watch(&self, wi: usize) -> WatchLiteralIndex;
    fn next_watch_mut(&mut self, wi: usize) -> &mut WatchLiteralIndex;
}

/// Note: this interface is based on ClauseIndex and Watch literal's position
/// in a clause.
pub trait ClauseWeaverIF {
    /// return the first watch literal index for literal `lit`
    fn get_watch_literal_index(&mut self, lit: Lit) -> WatchLiteralIndex;
    /// return a ClauseIndex of an unused clause
    fn get_free_index(&mut self) -> ClauseIndex;
    /// insert a watch to a watch list`
    fn insert_watch(&mut self, ci: ClauseIndex, wi: usize);
    /// O(1) remove the watch literal index of the watch literal index `wli`
    fn remove_watch(&mut self, wli: WatchLiteralIndex, lit: Lit) -> WatchLiteralIndex;
    /// O(1) remove function which remove the clause from two watcher lists
    fn remove_watches(&mut self, ci: ClauseIndex);
    /// instantiate a list of watch lists
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<WatchLiteralIndex>;
    /// unlink and link to freelist
    fn unweave(&mut self, ci: ClauseIndex);
    /// unlink and link to freelist
    fn unweave_sandbox(&mut self, ci: ClauseIndex);
}

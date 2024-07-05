use {crate::types::*, std::collections::HashSet};

pub trait WatcherLinkIF {
    fn next_watch(&self, wi: usize) -> WatchLiteralIndex;
    fn next_watch_mut(&mut self, wi: usize) -> &mut WatchLiteralIndex;
    // fn swap_watch_orders(&mut self);
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
    /// O(1) remove the *next* watch literal index of the watch literal index `wli`
    fn remove_next_watch(
        &mut self,
        wli: WatchLiteralIndex,
        next: WatchLiteralIndex,
        lit: Lit,
    ) -> ClauseIndex;
    /// O(n) remove function which remove the clause refered from `wli`
    fn remove_watches(&mut self, ci: ClauseIndex);
    /// link a clause `ci` to free list
    fn link_to_freelist(&mut self, ci: ClauseIndex);
    /// instantiate a list of watch lists
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<WatchLiteralIndex>;
    /// un-register a clause `cid` from alive clause database and make the clause dead.
    fn nullify_clause(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>);
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn nullify_clause_sandbox(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>);
    /// update watches of the clause
    fn reinitialize_nulls(&mut self, targets: &mut HashSet<Lit>);
}

// #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
// pub struct LinkHead {
//     pub next: ClauseIndex,
//     pub count: ClauseIndex,
//     pub timestamp: ClauseIndex,
// }

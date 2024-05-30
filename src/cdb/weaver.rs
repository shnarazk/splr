use {crate::types::*, std::collections::HashSet};

pub trait WatcherLinkIF {
    fn next_watch(&self, li: usize) -> WatchLiteralIndex;
    fn next_watch_mut(&mut self, li: usize) -> &WatchLiteralIndex;
    // fn swap_watch_orders(&mut self);
}

pub trait ClauseWeaverIF {
    fn get_watch_literal_index(&mut self, lit: Lit) -> WatchLiteralIndex;
    fn get_free_index(&mut self) -> ClauseIndex;
    /// insert a new watch index `wli` to the watch list for `lit`
    fn insert_watch(&mut self, wli: WatchLiteralIndex, lit: Lit);
    /// remove the *next* watch literal index of the watch literal index `wli`
    fn remove_next_watch(&mut self, wli: WatchLiteralIndex);
    /// O(n) remove function which remove the clause refered from `wli`
    fn remove_watch(&mut self, wli: WatchLiteralIndex);
    /// link a clause `ci` to free list
    fn mark_as_free(&mut self, ci: ClauseIndex);
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<ClauseIndex>;
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn nullify_clause(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>);
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn nullify_clause_sandbox(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>);
    /// update watches of the clause
    fn collect(&mut self, targets: &HashSet<Lit>);
}

// #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
// pub struct LinkHead {
//     pub next: ClauseIndex,
//     pub count: ClauseIndex,
//     pub timestamp: ClauseIndex,
// }

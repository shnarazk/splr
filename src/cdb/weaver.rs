use {crate::types::*, std::collections::HashSet};

pub trait WatcherLinkIF {
    fn next_watch(&self, li: usize) -> WatchLiteralIndex;
    fn next_watch_mut(&mut self, li: usize) -> &WatchLiteralIndex;
    // fn swap_watch_orders(&mut self);
}

pub trait ClauseWeaverIF {
    fn get_watcher_link(&mut self, lit: Lit) -> ClauseIndex;
    fn get_free_index(&mut self) -> ClauseIndex;
    fn insert_watcher(&mut self, ci: ClauseIndex, socond: bool, lit: Lit);
    fn remove_next_watcher(&mut self, ci: ClauseIndex, lit: Lit) -> bool;
    fn remove_watcher(&mut self, ci: ClauseIndex);
    fn mark_as_free(&mut self, index: ClauseIndex);
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<ClauseIndex>;
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn nullify_clause(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>);
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn nullify_clause_sandbox(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>);
    /// update watches of the clause
    fn collect(&mut self, targets: &HashSet<Lit>);
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinkHead {
    pub next: ClauseIndex,
    pub count: ClauseIndex,
    pub timestamp: ClauseIndex,
}

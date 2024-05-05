use {crate::types::*, std::collections::HashSet};

pub trait WatcherLinkIF {
    fn next_for_lit(&self, lit: Lit) -> ClauseIndex;
    fn next_for_lit_mut(&mut self, lit: Lit) -> &mut ClauseIndex;
    fn next_free(&self) -> ClauseIndex;
    fn next_free_mut(&mut self) -> &mut ClauseIndex;
    fn swap_watch_orders(&mut self);
}

pub trait ClauseWeaverIF {
    const HEAD_INDEX: usize = 0;
    const FREE_INDEX: usize = 0;
    fn get_watcher_link(&mut self, lit: Lit) -> ClauseIndex;
    fn get_free_index(&mut self) -> ClauseIndex;
    fn insert_watcher(&mut self, ci: ClauseIndex, socond: bool, lit: Lit);
    fn remove_next_watcher(&mut self, ci: ClauseIndex, lit: Lit) -> bool;
    fn remove_watcher(&mut self, ci: ClauseIndex);
    fn make_watches(num_vars: usize, clauses: &mut [Clause]) -> Vec<ClauseIndex>;
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn nullify_clause(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>);
    /// un-register a clause `cid` from clause database and make the clause dead.
    fn nullify_clause_sandbox(&mut self, ci: ClauseIndex, deads: &mut HashSet<Lit>);
    /// update watches of the clause
    fn collect_dead_watchers(&mut self, targets: &mut HashSet<Lit>);
    fn check_all_watchers_status(&self) -> Result<(), String>;
    fn check_watcher_status(&self, ci: ClauseIndex) -> Result<(), String>;
    fn check_chain_connectivity(&self, allow_dead: bool) -> Result<(), String>;
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinkHead {
    pub next: ClauseIndex,
    pub count: ClauseIndex,
    pub timestamp: ClauseIndex,
}

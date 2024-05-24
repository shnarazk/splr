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
    /// By picking up 1 for the free list, We can designate the list by `Lit 1` which
    /// is not used as a valid encoded lit.
    const FREE_INDEX: usize = 1;
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
    /// FIXME: this is not a good IF.
    fn check_all_watchers_status(&self) -> Result<(), String>;
    /// FIXME: this is not a good IF.
    fn check_watcher_status(&self, ci: ClauseIndex, should_be_dead: bool) -> Result<(), String>;
    /// FIXME: this is not a good IF.
    fn check_dead_watcher_status(&self, ci: ClauseIndex) -> Result<(), String>;
    /// FIXME: this is not a good IF.
    fn check_chain_connectivity(&self, allow_dead: bool) -> Result<(), String>;
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LinkHead {
    pub next: ClauseIndex,
    pub count: ClauseIndex,
    pub timestamp: ClauseIndex,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum WatcherState {
    // binary clauses are not watchers
    BinaryClause(bool),
    // Two watcher lists include a clause without DEAD flag.
    Alive,
    // it has DEAD flag and N watch lists contain this.
    Nullified(u8),
    // Free list contains this and any watcher list does not.
    #[default]
    Free,
    // Other weird cases
    Unsound,
}

/// FIXME: 2nd generation IF
pub trait WatcherStatusIF {
    fn get_watcher_status(&self, ci: ClauseIndex) -> WatcherState;
    /// whether a watcher link is a perfect loop (use 1 for free list).
    fn check_weaver(&self, lit: Lit) -> Result<(), String>;
    fn validate_watcher(&self, ci: ClauseIndex, acceptable: &[WatcherState]) -> Result<(), String>;
}

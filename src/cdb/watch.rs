use {super::ClauseId, crate::types::*, std::collections::HashMap};

/// API for 'watcher list' like [`register`](`crate::cdb::WatchDBIF::register`), [`detach`](`crate::cdb::WatchDBIF::detach`), [`update_blocker`](`crate::cdb::WatchDBIF::update_blocker`) and so on.
///
///## WATCHING LITERAL LIST MANAGEMENT RULES:
///  - Watching literals are lits[0] and lits[1] anytime anywhere.
///  - Watching literals must not be eliminated vars.
pub trait WatchDBIF {
    fn pop(&mut self) -> Option<(ClauseId, Lit)>;
}

impl WatchDBIF for HashMap<ClauseId, Lit> {
    fn pop(&mut self) -> Option<(ClauseId, Lit)> {
        if let Some(&k) = self.keys().next() {
            return self.remove_entry(&k);
        }
        None
    }
}

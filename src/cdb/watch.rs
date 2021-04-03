use {super::ClauseId, crate::types::*};

/// API for 'watcher list' like [`register`](`crate::cdb::WatchDBIF::register`), [`detach`](`crate::cdb::WatchDBIF::detach`), [`update_blocker`](`crate::cdb::WatchDBIF::update_blocker`) and so on.
pub trait WatchDBIF {
    /// make a new 'watch', and add it to this watcher list.
    fn register(&mut self, w: Watch);
    /// remove *n*-th clause from the watcher list. *O(1)* operation.
    fn detach(&mut self, n: usize) -> Watch;
    /// remove a clause which id is `cid` from the watcher list. *O(n)* operation.
    fn detach_with(&mut self, cid: ClauseId) -> Option<Watch>;
    /// update blocker of cid.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit) -> MaybeInconsistent;
}

/// 'Watch literal' structure
#[derive(Clone, Debug)]
pub struct Watch {
    /// a cache of a literal in the clause
    pub blocker: Lit,
    /// ClauseId
    pub c: ClauseId,
}

impl Default for Watch {
    fn default() -> Watch {
        Watch {
            blocker: NULL_LIT,
            c: ClauseId::default(),
        }
    }
}

impl WatchDBIF for Vec<Watch> {
    fn register(&mut self, w: Watch) {
        self.push(w);
    }
    fn detach(&mut self, n: usize) -> Watch {
        self.swap_remove(n)
    }
    fn detach_with(&mut self, cid: ClauseId) -> Option<Watch> {
        for (n, w) in self.iter().enumerate() {
            if w.c == cid {
                return Some(self.swap_remove(n));
            }
        }
        None
    }
    /// This O(n) function is used only in Eliminator. So the cost can be ignored.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit) -> MaybeInconsistent {
        for w in &mut self[..] {
            if w.c == cid {
                w.blocker = l;
                return;
            }
        }
    }
}

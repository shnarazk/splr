use {super::ClauseId, crate::types::*, std::collections::VecDeque};

/// API for 'watcher list' like `attach`, `detach`, `detach_with` and so on.
pub trait WatchDBIF {
    /// make a new 'watch', and add it to this watcher list.
    fn register(&mut self, blocker: Lit, c: ClauseId, front: bool);
    /// remove *n*-th clause from the watcher list. *O(1)* operation.
    fn detach(&mut self, n: usize);
    /// remove a clause which id is `cid` from the watcher list. *O(n)* operation.
    fn detach_with(&mut self, cid: ClauseId);
    /// update blocker of cid.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit);
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
    fn register(&mut self, blocker: Lit, c: ClauseId, _front: bool) {
        self.push(Watch { blocker, c });
    }
    fn detach(&mut self, n: usize) {
        self.swap_remove(n);
    }
    fn detach_with(&mut self, cid: ClauseId) {
        for (n, w) in self.iter().enumerate() {
            if w.c == cid {
                self.swap_remove(n);
                return;
            }
        }
        #[cfg(feature = "boundary_check")]
        panic!("detach_with failed to seek");
    }
    /// This O(n) function is used only in Eliminator. So the cost can be ignored.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit) {
        for w in &mut self[..] {
            if w.c == cid {
                w.blocker = l;
                return;
            }
        }
    }
}

pub type WatchList = VecDeque<Watch>;

impl WatchDBIF for WatchList {
    fn register(&mut self, blocker: Lit, c: ClauseId, front: bool) {
        if front {
            self.push_front(Watch { blocker, c });
        } else {
            self.push_back(Watch { blocker, c });
        }
    }
    fn detach(&mut self, n: usize) {
        self.swap_remove_back(n);
    }
    fn detach_with(&mut self, cid: ClauseId) {
        for (n, w) in self.iter().enumerate() {
            if w.c == cid {
                self.swap_remove_back(n);
                return;
            }
        }
        #[cfg(feature = "boundary_check")]
        panic!("detach_with failed to seek");
    }
    /// This O(n) function is used only in Eliminator. So the cost can be ignored.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit) {
        for w in self.iter_mut() {
            if w.c == cid {
                w.blocker = l;
                return;
            }
        }
    }
}

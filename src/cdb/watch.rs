use {super::ClauseId, crate::types::*};

/// API for 'watcher list' like `attach`, `detach`, `detach_with` and so on.
pub trait WatchDBIF {
    /// make a new 'watch', and add it to this watcher list.
    fn register(&mut self, blocker: Lit, c: ClauseId, binary: bool);
    /// remove *n*-th clause from the watcher list. *O(1)* operation.
    fn detach(&mut self, n: usize);
    /// remove a clause which id is `cid` from the watcher list. *O(n)* operation.
    fn detach_with(&mut self, cid: ClauseId);
    /// update blocker of cid.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit, binary: bool);
}

/// 'Watch literal' structure
#[derive(Clone, Debug)]
pub struct Watch {
    /// a cache of a literal in the clause
    pub blocker: Lit,
    /// ClauseId
    pub c: ClauseId,
    /// whether clause is binary.
    pub binary: bool,
}

impl Default for Watch {
    fn default() -> Watch {
        Watch {
            blocker: NULL_LIT,
            c: ClauseId::default(),
            binary: false,
        }
    }
}

impl WatchDBIF for Vec<Watch> {
    fn register(&mut self, blocker: Lit, c: ClauseId, binary: bool) {
        self.push(Watch { blocker, c, binary });
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
    }
    /// This O(n) function is used only in Eliminator. So the cost can be ignored.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit, binary: bool) {
        for w in &mut self[..] {
            if w.c == cid {
                w.blocker = l;
                w.binary = binary;
                return;
            }
        }
    }
}

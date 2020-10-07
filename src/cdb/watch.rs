use {
    super::ClauseId,
    crate::types::*,
    std::{cmp::Ordering, collections::BinaryHeap},
};

/// API for 'watcher list' like `attach`, `detach`, `detach_with` and so on.
pub trait WatchDBIF {
    /// make a new 'watch', and add it to this watcher list.
    fn register(&mut self, activity: usize, blocker: Lit, c: ClauseId);
    /// remove *n*-th clause from the watcher list. *O(1)* operation.
    fn detach(&mut self, n: usize);
    /// remove a clause which id is `cid` from the watcher list. *O(n)* operation.
    fn detach_with(&mut self, cid: ClauseId);
    /// update blocker of cid.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit);
    /// return an empty db which has the same type of self.
    fn empty_copy(&self) -> Self;
}

/// 'Watch literal' structure
#[derive(Clone, Debug)]
pub struct Watch {
    /// importance of the clause
    pub activity: usize,
    /// a cache of a literal in the clause
    pub blocker: Lit,
    /// ClauseId
    pub c: ClauseId,
}

impl PartialEq for Watch {
    fn eq(&self, other: &Self) -> bool {
        self.c == other.c
    }
}

impl Eq for Watch {}
impl PartialOrd for Watch {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.activity.partial_cmp(&other.activity)
    }
}

impl Ord for Watch {
    fn cmp(&self, other: &Self) -> Ordering {
        self.activity.cmp(&other.activity)
    }
}

impl Default for Watch {
    fn default() -> Watch {
        Watch {
            activity: 0,
            blocker: NULL_LIT,
            c: ClauseId::default(),
        }
    }
}

impl WatchDBIF for BinaryHeap<Watch> {
    fn register(&mut self, activity: usize, blocker: Lit, c: ClauseId) {
        self.push(Watch {
            activity,
            blocker,
            c,
        });
    }
    fn detach(&mut self, _n: usize) {
        todo!()
    }
    fn detach_with(&mut self, cid: ClauseId) {
        let mut nw = BinaryHeap::<Watch>::new();
        for w in self.drain() {
            if w.c != cid {
                nw.push(w);
            }
        }
        std::mem::swap(&mut nw, self);
    }
    /// This O(n) function is used only in Eliminator. So the cost can be ignored.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit) {
        let mut nw = BinaryHeap::<Watch>::new();
        for mut w in self.drain() {
            if w.c == cid {
                w.blocker = l;
                nw.push(w);
            }
        }
        std::mem::swap(&mut nw, self);
    }
    fn empty_copy(&self) -> Self {
        BinaryHeap::<Watch>::new()
    }
}

impl WatchDBIF for Vec<Watch> {
    fn register(&mut self, activity: usize, blocker: Lit, c: ClauseId) {
        self.push(Watch {
            activity,
            blocker,
            c,
        });
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
    fn empty_copy(&self) -> Self {
        Vec::<Watch>::new()
    }
}

pub type WatchList = BinaryHeap<Watch>;

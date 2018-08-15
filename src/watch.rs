use types::*;

/// In splr, the watch map is reseted at the beginning of every simplification phase.
/// It's just a immutable index (with some data) referring to a Clause in a Vec.
#[derive(Debug, PartialEq)]
pub struct Watch {
    pub other: Lit,
    pub by: ClauseIndex,
    pub to: Lit,
    pub swap: usize,
}

impl Watch {
    pub fn new(o: Lit, b: ClauseIndex) -> Watch {
        Watch {
            other: o,
            by: b,
            to: NULL_LIT,
            swap: 0,
        }
    }
}

/// is a mapping from `Lit` to `Vec<Watch>`.
pub type WatchMap = Vec<Vec<Watch>>;

/// returns `WatchMap`, or `Vec<Vec<Watch>>`.
pub fn new_watch_map(nv: usize) -> WatchMap {
    let size = 2 * (nv + 1);
    let mut vec = Vec::with_capacity(size);
    for _i in 0..size {
        vec.push(Vec::with_capacity(40));
    }
    vec
}

pub fn set_watch(w: &mut [Vec<Watch>], ci: ClauseIndex, w0: Lit, w1: Lit) -> () {
    if ci == NULL_CLAUSE {
        return;
    }
    w[w0.negate() as usize].push(Watch::new(w1, ci));
    w[w1.negate() as usize].push(Watch::new(w0, ci));
}

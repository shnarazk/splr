use {
    super::{weaver::WatchLiteralIndexRef, WatcherLinkIF},
    crate::{assign::AssignIF, types::*},
    std::{
        collections::HashSet,
        fmt,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::Iter,
    },
};

/// API for Clause, providing literal accessors.
pub trait ClauseIF {
    /// return true if it contains no literals; a clause after unit propagation.
    fn is_dead(&self) -> bool;
    /// return 1st watch
    fn lit0(&self) -> Lit;
    /// return 2nd watch
    fn lit1(&self) -> Lit;
    /// return `true` if the clause contains the literal
    fn contains(&self, lit: Lit) -> bool;
    /// check clause satisfiability
    fn is_satisfied_under(&self, asg: &impl AssignIF) -> bool;
    /// return an iterator over its literals.
    fn iter(&self) -> Iter<'_, Lit>;
    /// return the number of literals.
    fn len(&self) -> usize;
    /// just for cargo clippy
    fn is_empty(&self) -> usize;

    #[cfg(feature = "boundary_check")]
    /// return timestamp.
    fn timestamp(&self) -> usize;
    #[cfg(feature = "boundary_check")]
    fn set_birth(&mut self, time: usize);
}

/// A representation of 'clause'
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd)]
pub struct Clause {
    /// links. Note: watch0 is also used as freelist
    pub(super) links: [WatchLiteralIndexRef; 2],
    /// The literals in a clause.
    pub(super) lits: Vec<Lit>,
    /// Flags (8 bits)
    pub(super) flags: FlagClause,
    /// A static clause evaluation criterion like LBD, NDD, or something.
    pub rank: u16,
    /// A record of the rank at previos stage.
    pub rank_old: u16,
    /// the index from which `propagate` starts searching an un-falsified literal.
    /// Since it's just a hint, we don't need u32 or usize.
    pub search_from: u16,

    #[cfg(any(feature = "boundary_check", feature = "clause_rewarding"))]
    /// the number of conflicts at which this clause was used in `conflict_analyze`
    timestamp: usize,

    #[cfg(feature = "clause_rewarding")]
    /// A dynamic clause evaluation criterion based on the number of references.
    reward: f64,

    #[cfg(feature = "boundary_check")]
    pub birth: usize,
    #[cfg(feature = "boundary_check")]
    pub moved_at: Propagate,
}

impl Default for Clause {
    fn default() -> Clause {
        Clause {
            links: [
                WatchLiteralIndexRef::default(),
                WatchLiteralIndexRef::default(),
            ],
            lits: vec![Lit::default(), Lit::default()],
            flags: FlagClause::empty(),
            rank: 0,
            rank_old: 0,
            search_from: 2,

            #[cfg(any(feature = "boundary_check", feature = "clause_rewarding"))]
            timestamp: 0,

            #[cfg(feature = "clause_rewarding")]
            reward: 0.0,

            #[cfg(feature = "boundary_check")]
            birth: 0,
            #[cfg(feature = "boundary_check")]
            moved_at: Propagate::None,
        }
    }
}

impl Index<usize> for Clause {
    type Output = Lit;
    fn index(&self, i: usize) -> &Lit {
        &self.lits[i]
    }
}

impl IndexMut<usize> for Clause {
    fn index_mut(&mut self, i: usize) -> &mut Lit {
        &mut self.lits[i]
    }
}

impl Index<Range<usize>> for Clause {
    type Output = [Lit];
    fn index(&self, r: Range<usize>) -> &[Lit] {
        &self.lits[r]
    }
}

impl Index<RangeFrom<usize>> for Clause {
    type Output = [Lit];
    fn index(&self, r: RangeFrom<usize>) -> &[Lit] {
        &self.lits[r]
    }
}

impl IndexMut<Range<usize>> for Clause {
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Lit] {
        &mut self.lits[r]
    }
}

impl IndexMut<RangeFrom<usize>> for Clause {
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Lit] {
        &mut self.lits[r]
    }
}

impl<'a> IntoIterator for &'a Clause {
    type Item = &'a Lit;
    type IntoIter = Iter<'a, Lit>;
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl<'a> IntoIterator for &'a mut Clause {
    type Item = &'a Lit;
    type IntoIter = Iter<'a, Lit>;
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl From<&Clause> for Vec<i32> {
    fn from(c: &Clause) -> Vec<i32> {
        c.lits.iter().map(|l| i32::from(*l)).collect::<Vec<i32>>()
    }
}

impl ClauseIF for Clause {
    fn is_dead(&self) -> bool {
        self.is(FlagClause::DEAD)
    }
    fn iter(&self) -> Iter<'_, Lit> {
        self.lits.iter()
    }
    #[inline]
    fn lit0(&self) -> Lit {
        self.lits[0]
    }
    #[inline]
    fn lit1(&self) -> Lit {
        self.lits[1]
    }
    fn contains(&self, lit: Lit) -> bool {
        self.lits.contains(&lit)
    }
    fn is_satisfied_under(&self, asg: &impl AssignIF) -> bool {
        for l in self.lits.iter() {
            if asg.assigned(*l) == Some(true) {
                return true;
            }
        }
        false
    }
    fn len(&self) -> usize {
        self.lits.len()
    }
    fn is_empty(&self) -> usize {
        unimplemented!()
    }

    #[cfg(feature = "boundary_check")]
    /// return timestamp.
    fn timestamp(&self) -> usize {
        self.timestamp
    }
    #[cfg(feature = "boundary_check")]
    fn set_birth(&mut self, time: usize) {
        self.birth = time;
    }
}

impl FlagIF for Clause {
    type FlagType = FlagClause;
    #[inline]
    fn is(&self, flag: Self::FlagType) -> bool {
        self.flags.contains(flag)
    }
    #[inline]
    fn set(&mut self, f: Self::FlagType, b: bool) {
        self.flags.set(f, b);
    }
    #[inline]
    fn turn_off(&mut self, flag: Self::FlagType) {
        self.flags.remove(flag);
    }
    #[inline]
    fn turn_on(&mut self, flag: Self::FlagType) {
        self.flags.insert(flag);
    }
    #[inline]
    fn toggle(&mut self, flag: Self::FlagType) {
        self.flags.toggle(flag);
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        #[cfg(feature = "boundary_check")]
        {
            let st = |flag, mes| if self.is(flag) { mes } else { "" };
            write!(
                f,
                "{{{:?}b{}{}{}}}",
                i32s(&self.lits),
                self.birth,
                st(FlagClause::LEARNT, ", learnt"),
                st(FlagClause::ENQUEUED, ", enqueued"),
            )
        }
        #[cfg(not(feature = "boundary_check"))]
        {
            let st = |flag, mes| if self.is(flag) { mes } else { "" };
            write!(
                f,
                "{{{:?}{}{}}}",
                i32s(&self.lits),
                st(FlagClause::LEARNT, ", learnt"),
                st(FlagClause::ENQUEUED, ", enqueued"),
            )
        }
    }
}

impl WatcherLinkIF for Clause {
    fn next_watch(&self, wi: usize) -> WatchLiteralIndex {
        self.links[wi].next
    }
    fn prev_watch(&self, wi: usize) -> WatchLiteralIndex {
        self.links[wi].prev
    }
    fn next_watch_mut(&mut self, wi: usize) -> &mut WatchLiteralIndex {
        &mut self.links[wi].next
    }
    fn prev_watch_mut(&mut self, wi: usize) -> &mut WatchLiteralIndex {
        &mut self.links[wi].prev
    }
}

impl Clause {
    /// update rank field with the present LBD.
    // If it's big enough, skip the loop.
    pub fn update_lbd(&mut self, asg: &impl AssignIF, _lbd_temp: &mut [usize]) -> usize {
        let base_level = asg.root_level();
        let mut rank = 0;
        let mut levels: HashSet<DecisionLevel> = HashSet::new();
        for lit in self.lits.iter() {
            let lv = asg.level(lit.vi());
            if lv == base_level {
                rank += 1;
            } else {
                levels.insert(lv);
            }
        }
        rank += levels.len();
        /*
        let rank = self
            .lits
            .iter()
            .map(|l| asg.level(l.vi()))
            .filter(|l| *l != base_level)
            .collect::<HashSet<DecisionLevel>>()
            .len();
        */
        self.rank = rank as u16;
        rank
        // if 8192 <= self.lits.len() {
        //     self.rank = u16::MAX;
        //     return u16::MAX as usize;
        // }
        // let key: usize = lbd_temp[0] + 1;
        // lbd_temp[0] = key;
        // let mut cnt = 0;
        // for l in &self.lits {
        //     let lv = asg.level(l.vi());
        //     if lv == 0 {
        //         continue;
        //     }
        //     let p = &mut lbd_temp[lv as usize];
        //     if *p != key {
        //         *p = key;
        //         cnt += 1;
        //     }
        // }
        // self.rank = cnt;
        // cnt as usize
    }
}

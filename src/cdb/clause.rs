use {
    crate::types::*,
    std::{
        fmt,
        ops::{Index, IndexMut},
        slice::Iter,
    },
};

/// A representation of 'clause'
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd)]
pub struct Clause<'a> {
    /// The literals in a clause.
    pub(super) lits: Vec<Lit<'a>>,
    /// Flags (8 bits)
    pub(crate) flags: FlagClause,
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

/// API for Clause, providing literal accessors.
pub trait ClauseIF<'a> {
    /// return true if it contains no literals; a clause after unit propagation.
    fn is_empty(&'a self) -> bool;
    /// return true if it contains no literals; a clause after unit propagation.
    fn is_dead(&'a self) -> bool;
    /// return 1st watch
    fn lit0(&'a self) -> Lit<'a>;
    /// return 2nd watch
    fn lit1(&'a self) -> Lit<'a>;
    /// return `true` if the clause contains the literal
    fn contains(&'a self, lit: Lit<'a>) -> bool;
    /// check clause satisfiability
    fn is_satisfied_under(&'a self) -> bool;
    /// return an iterator over its literals.
    fn iter(&'a self) -> Iter<'a, Lit<'a>>;
    /// return the number of literals.
    fn len(&self) -> usize;

    #[cfg(feature = "boundary_check")]
    /// return timestamp.
    fn timestamp(&self) -> usize;
    #[cfg(feature = "boundary_check")]
    fn set_birth(&mut self, time: usize);
}

impl Default for Clause<'_> {
    fn default() -> Clause<'static> {
        Clause {
            lits: vec![],
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

impl<'a> Index<usize> for Clause<'a> {
    type Output = Lit<'a>;
    #[inline]
    fn index(&self, i: usize) -> &Lit<'a> {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.lits.get_unchecked(i)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.lits[i]
    }
}

impl<'a> IndexMut<usize> for Clause<'a> {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Lit<'a> {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.lits.get_unchecked_mut(i)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.lits[i]
    }
}

// impl<'a> Index<Range<usize>> for Clause<'a> {
//     type Output = [Lit<'a>];
//     #[inline]
//     fn index(&'a self, r: Range<usize>) -> &'a [Lit<'a>] {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.lits.get_unchecked(r)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self.lits[r]
//     }
// }

// impl<'a> Index<RangeFrom<usize>> for Clause<'a> {
//     type Output = [Lit<'a>];
//     #[inline]
//     fn index(&'a self, r: RangeFrom<usize>) -> &'a [Lit<'a>] {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.lits.get_unchecked(r)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &self.lits[r]
//     }
// }

// impl<'a> IndexMut<Range<usize>> for Clause<'a> {
//     #[inline]
//     fn index_mut(&mut self, r: Range<usize>) -> &'a mut [Lit<'a>] {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.lits.get_unchecked_mut(r)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self.lits[r]
//     }
// }

// impl<'a> IndexMut<RangeFrom<usize>> for Clause<'a> {
//     #[inline]
//     fn index_mut(&mut self, r: RangeFrom<usize>) -> &'a mut [Lit<'a>] {
//         #[cfg(feature = "unsafe_access")]
//         unsafe {
//             self.lits.get_unchecked_mut(r)
//         }
//         #[cfg(not(feature = "unsafe_access"))]
//         &mut self.lits[r]
//     }
// }

impl<'a> IntoIterator for &'a Clause<'a> {
    type Item = &'a Lit<'a>;
    type IntoIter = Iter<'a, Lit<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl<'a> IntoIterator for &'a mut Clause<'a> {
    type Item = &'a Lit<'a>;
    type IntoIter = Iter<'a, Lit<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        self.lits.iter()
    }
}

impl<'a> From<&'a Clause<'a>> for Vec<i32> {
    fn from(c: &'a Clause) -> Vec<i32> {
        c.lits.iter().map(|l| i32::from(*l)).collect::<Vec<i32>>()
    }
}

impl<'a> ClauseIF<'a> for Clause<'a> {
    fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }
    fn is_dead(&'a self) -> bool {
        self.lits.is_empty()
    }
    fn iter(&'a self) -> Iter<'a, Lit<'a>> {
        self.lits.iter()
    }
    #[inline]
    fn lit0(&'a self) -> Lit<'a> {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            *self.lits.get_unchecked(0)
        }
        #[cfg(not(feature = "unsafe_access"))]
        self.lits[0]
    }
    #[inline]
    fn lit1(&'a self) -> Lit<'a> {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            *self.lits.get_unchecked(1)
        }
        #[cfg(not(feature = "unsafe_access"))]
        self.lits[1]
    }
    fn contains(&'a self, lit: Lit<'a>) -> bool {
        self.lits.contains(&lit)
    }
    fn is_satisfied_under(&'a self) -> bool {
        for l in self.lits.iter() {
            if l.assigned() == Some(true) {
                return true;
            }
        }
        false
    }
    fn len(&self) -> usize {
        self.lits.len()
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

impl FlagIF for Clause<'_> {
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

impl fmt::Display for Clause<'_> {
    #[cfg(feature = "boundary_check")]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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

impl Clause<'_> {
    /// update rank field with the present LBD.
    // If it's big enough, skip the loop.
    pub fn update_lbd(&mut self, lbd_temp: &mut [usize]) -> usize {
        if 8192 <= self.lits.len() {
            self.rank = u16::MAX;
            return u16::MAX as usize;
        }
        let key: usize = lbd_temp[0] + 1;
        lbd_temp[0] = key;
        let mut cnt = 0;
        for l in &self.lits {
            let lv = l.var.level;
            if lv == 0 {
                continue;
            }
            let p = &mut lbd_temp[lv as usize];
            if *p != key {
                *p = key;
                cnt += 1;
            }
        }
        self.rank = cnt;
        cnt as usize
    }
}

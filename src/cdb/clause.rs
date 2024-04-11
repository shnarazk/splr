use {
    crate::{assign::AssignIF, cdb::DoubleLink, types::*},
    std::{
        fmt,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::Iter,
    },
};

impl Default for Clause {
    fn default() -> Clause {
        Clause {
            watch0: DoubleLink::default(),
            watch1: DoubleLink::default(),
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

impl Index<usize> for Clause {
    type Output = Lit;
    #[inline]
    fn index(&self, i: usize) -> &Lit {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.lits.get_unchecked(i)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.lits[i]
    }
}

impl IndexMut<usize> for Clause {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Lit {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.lits.get_unchecked_mut(i)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.lits[i]
    }
}

impl Index<Range<usize>> for Clause {
    type Output = [Lit];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Lit] {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.lits.get_unchecked(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.lits[r]
    }
}

impl Index<RangeFrom<usize>> for Clause {
    type Output = [Lit];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Lit] {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.lits.get_unchecked(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.lits[r]
    }
}

impl IndexMut<Range<usize>> for Clause {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Lit] {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.lits.get_unchecked_mut(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.lits[r]
    }
}

impl IndexMut<RangeFrom<usize>> for Clause {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Lit] {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.lits.get_unchecked_mut(r)
        }
        #[cfg(not(feature = "unsafe_access"))]
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
    fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }
    fn is_dead(&self) -> bool {
        self.lits.is_empty()
    }
    fn iter(&self) -> Iter<'_, Lit> {
        self.lits.iter()
    }
    #[inline]
    fn lit0(&self) -> Lit {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            *self.lits.get_unchecked(0)
        }
        #[cfg(not(feature = "unsafe_access"))]
        self.lits[0]
    }
    #[inline]
    fn lit1(&self) -> Lit {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            *self.lits.get_unchecked(1)
        }
        #[cfg(not(feature = "unsafe_access"))]
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

impl Clause {
    /// update rank field with the present LBD.
    // If it's big enough, skip the loop.
    pub fn update_lbd(&mut self, asg: &impl AssignIF, lbd_temp: &mut [usize]) -> usize {
        if 8192 <= self.lits.len() {
            self.rank = u16::MAX;
            return u16::MAX as usize;
        }
        let key: usize = lbd_temp[0] + 1;
        lbd_temp[0] = key;
        let mut cnt = 0;
        for l in &self.lits {
            let lv = asg.level(l.vi());
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

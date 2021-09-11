use {
    crate::{assign::AssignIF, types::*},
    std::{
        fmt,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::Iter,
    },
};

impl Default for Clause {
    fn default() -> Clause {
        Clause {
            lits: vec![],
            flags: Flag::empty(),
            rank: 0,
            search_from: 2,
            reward: 0.0,
            timestamp: 0,

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
    fn is_satisfied_under<A>(&self, asg: &A) -> bool
    where
        A: AssignIF,
    {
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
    fn timestamp(&self) -> usize {
        self.timestamp
    }
    fn to_vivify(&self, initial_stage: bool) -> Option<f64> {
        if initial_stage {
            (!self.is_dead()).then(|| self.len() as f64)
        } else {
            (!self.is_dead()
                && self.is(Flag::VIVIFIED)
                && self.is(Flag::VIVIFIED2)
                && (self.is(Flag::LEARNT) || self.is(Flag::DERIVE20)))
            .then(|| self.reward)
        }
    }
    fn vivified(&mut self) {
        self.turn_on(Flag::VIVIFIED);
        self.turn_off(Flag::VIVIFIED2);
        if !self.is(Flag::LEARNT) {
            self.turn_off(Flag::DERIVE20);
        }
    }

    #[cfg(feature = "boundary_check")]
    fn set_birth(&mut self, time: usize) {
        self.birth = time;
    }
}

impl FlagIF for Clause {
    fn is(&self, flag: Flag) -> bool {
        self.flags.contains(flag)
    }
    fn set(&mut self, f: Flag, b: bool) {
        self.flags.set(f, b);
    }
    fn toggle(&mut self, flag: Flag) {
        self.flags.toggle(flag);
    }
    fn turn_off(&mut self, flag: Flag) {
        self.flags.remove(flag);
    }
    fn turn_on(&mut self, flag: Flag) {
        self.flags.insert(flag);
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
            st(Flag::LEARNT, ", learnt"),
            st(Flag::ENQUEUED, ", enqueued"),
        )
    }
    #[cfg(not(feature = "boundary_check"))]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(
            f,
            "{{{:?}{}{}}}",
            i32s(&self.lits),
            st(Flag::LEARNT, ", learnt"),
            st(Flag::ENQUEUED, ", enqueued"),
        )
    }
}

impl Clause {
    /// update rank field with the present LBD.
    pub fn update_lbd<A>(&mut self, asg: &A, lbd_temp: &mut [usize]) -> usize
    where
        A: AssignIF,
    {
        let level = asg.level_ref();
        let key: usize = lbd_temp[0] + 1;
        lbd_temp[0] = key;
        let mut cnt = 0;
        for l in &self.lits {
            let lv = level[l.vi()];
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

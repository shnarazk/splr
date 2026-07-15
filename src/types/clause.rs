use {
    crate::{assign::AssignIF, types::*},
    std::{
        fmt,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::Iter,
    },
};

/// A representation of 'clause'
#[derive(Clone, Debug)]
pub struct Clause {
    /// The literals in a clause.
    pub(crate) lits: Vec<Lit>,
    /// Flags (8 bits)
    pub(crate) flags: FlagClause,
    /// the index from which `propagate` starts searching an un-falsified literal.
    /// Since it's just a hint, we don't need u32 or usize.
    pub search_from: u16,
    /// The last reference time in conflict analysis
    pub(crate) referred_at: usize,
    /// The minimal decision level at which a conflict occured by this clause
    pub(crate) reference_height: DecisionLevel,
    /// last vivified time in conflicts
    pub(crate) vivify_age: usize,
    // last vivified time in conflict
    pub(crate) vivify_at: usize,
    /// the minimal lbd of this clause so far
    pub(crate) lbd: DecisionLevel,
}

/// API for Clause, providing literal accessors.
pub trait ClauseIF {
    /// return true if it contains no literals; a clause after unit propagation.
    fn is_empty(&self) -> bool;
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
    /// return true is this is a unit clause under `asg`.
    fn is_unit_under(&self, asg: &impl AssignIF) -> bool;
    /// update reference_distance.
    fn update_reference(&mut self, asg: &mut impl AssignIF);
}

impl Default for Clause {
    fn default() -> Clause {
        Clause {
            lits: vec![],
            flags: FlagClause::empty(),
            search_from: 2,
            referred_at: 0,
            reference_height: DecisionLevel::MAX,
            vivify_age: 0,
            vivify_at: 0,
            lbd: DecisionLevel::MAX,
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
    fn is_unit_under(&self, asg: &impl AssignIF) -> bool {
        let unassigned = self
            .lits
            .iter()
            .filter(|l| asg.assigned(**l).is_none())
            .count();
        let all_others_false = self
            .lits
            .iter()
            .filter(|l| asg.assigned(**l).is_some())
            .all(|l| asg.assigned(*l) == Some(false));
        unassigned == 1 && all_others_false
    }
    fn update_reference(&mut self, asg: &mut impl AssignIF) {
        self.referred_at = asg.current_conflict_index();
        let level = asg.decision_level();
        self.lbd = self.lbd.min(asg.literal_block_distance_current(&self.lits));
        self.reference_height = self.reference_height.min(level);
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

// A generic reference to a clause or something else.
// we can use DEAD for simply satisfied form, f.e. an empty forms,
// while EmptyClause can be used for simply UNSAT form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RefClause {
    Clause(ClauseId),
    Dead,
    EmptyClause,
    RegisteredClause(ClauseId),
    UnitClause(Lit),
}

impl RefClause {
    pub fn as_cid(&self) -> ClauseId {
        match self {
            RefClause::Clause(cid) => *cid,
            RefClause::RegisteredClause(cid) => *cid,
            _ => panic!("invalid reference to clause"),
        }
    }
    pub fn is_new(&self) -> Option<ClauseId> {
        match self {
            RefClause::Clause(cid) => Some(*cid),
            RefClause::RegisteredClause(_) => None,
            RefClause::EmptyClause => None,
            RefClause::Dead => None,
            RefClause::UnitClause(_) => None,
        }
    }
}

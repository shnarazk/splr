/// Crate `clause` provides `clause` object and its manager `ClauseDB`
use {
    crate::{
        assign::AssignIF,
        eliminate::EliminateIF,
        state::{SearchStrategy, State},
        types::*,
        var::VarDBIF,
    },
    std::{
        cmp::Ordering,
        fmt,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::{Iter, IterMut},
    },
};

/// API for Clause, providing literal accessors.
pub trait ClauseIF {
    /// return true if it contains no literals; a clause after unit propagation.
    fn is_empty(&self) -> bool;
    /// return an iterator over its literals.
    fn iter(&self) -> Iter<'_, Lit>;
    /// return the number of literals.
    fn len(&self) -> usize;
}

/// API for clause management like `reduce`, `simplify`, `new_clause`, and so on.
pub trait ClauseDBIF: IndexMut<ClauseId, Output = Clause> {
    /// return the length of `clause`.
    fn len(&self) -> usize;
    /// return true if it's empty.
    fn is_empty(&self) -> bool;
    /// return an iterator.
    fn iter(&self) -> Iter<'_, Clause>;
    /// return an mutable iterator.
    fn iter_mut(&mut self) -> IterMut<'_, Clause>;
    /// return a watcher list
    fn watcher_list(&self, l: Lit) -> &[Watch];
    /// return the list of watch lists
    fn watcher_lists_mut(&mut self) -> &mut [Vec<Watch>];
    /// unregister a clause `cid` from clause database and make the clause dead.
    fn detach(&mut self, cid: ClauseId);
    /// check a condition to reduce.
    /// * return `true` if ruduction is done.
    /// * Otherwise return `false`.
    ///
    /// # CAVEAT
    /// *precondition*: decision level == 0.
    fn check_and_reduce<V>(&mut self, vdb: &mut V, nc: usize) -> bool
    where
        V: VarDBIF;
    fn reset(&mut self);
    /// delete *dead* clauses from database, which are made by:
    /// * `reduce`
    /// * `simplify`
    /// * `kill`
    fn garbage_collect(&mut self);
    /// allocate a new clause and return its id.
    /// * If 2nd arg is `Some(vdb)`, register `v` as a learnt after sorting based on assign level.
    /// * Otherwise, register `v` as a permanent clause, which rank is zero.
    fn new_clause<A, V>(
        &mut self,
        asgs: &mut A,
        v: &mut [Lit],
        level_sort: Option<&mut V>,
    ) -> ClauseId
    where
        A: AssignIF,
        V: VarDBIF;
    /// check and convert a learnt clause to permanent if needed.
    fn convert_to_permanent<A>(&mut self, asgs: &mut A, cid: ClauseId) -> bool
    where
        A: AssignIF;
    /// return the number of alive clauses in the database. Or return the database size if `active` is `false`.
    fn count(&self, alive: bool) -> usize;
    /// return the number of clauses which satisfy given flags and aren't DEAD.
    fn countf(&self, mask: Flag) -> usize;
    /// record a clause to unsat certification.
    fn certificate_add(&mut self, vec: &[Lit]);
    /// record a deleted clause to unsat certification.
    fn certificate_delete(&mut self, vec: &[Lit]);
    /// delete satisfied clauses at decision level zero.
    fn eliminate_satisfied_clauses<E, V>(&mut self, elim: &mut E, vdb: &mut V, occur: bool)
    where
        E: EliminateIF,
        V: VarDBIF;
    /// flag positive and negative literals of a var as dirty
    fn touch_var(&mut self, vi: VarId);
    /// check the number of clauses
    /// * `Err(SolverError::OutOfMemory)` -- the db size is over the limit.
    /// * `Ok(true)` -- enough small
    /// * `Ok(false)` -- close to the limit
    fn check_size(&self) -> Result<bool, SolverError>;
    /// returns None if the given assignment is a model of a problem.
    /// Otherwise returns a clause which is not satisfiable under a given assignment.
    /// Clauses with an unassigned literal are treated as falsified in `strict` mode.
    fn validate<V>(&self, vdb: &V, strict: bool) -> Option<ClauseId>
    where
        V: VarDBIF;
    /// removes Lit `p` from Clause *self*. This is an O(n) function!
    /// returns true if the clause became a unit clause.
    /// Called only from strengthen_clause
    fn strengthen(&mut self, cid: ClauseId, p: Lit) -> bool;
}

/// API for Clause Id.
pub trait ClauseIdIF {
    /// return `true` if a given clause id is made from a `Lit`.
    fn is_lifted_lit(self) -> bool;
}

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

/// Record of clause operations to build DRAT certifications.
#[derive(Debug, Eq, PartialEq)]
pub enum CertifiedRecord {
    /// placed at the end.
    SENTINEL,
    /// added a (learnt) clause.
    ADD,
    /// deleted a clause.
    DELETE,
}

type DRAT = Vec<(CertifiedRecord, Vec<i32>)>;

/// 'Clause' Identifier, or 'clause' index, starting with one.
/// Note: ids are re-used after 'garbage collection'.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ClauseId {
    /// a sequence number.
    pub ordinal: u32,
}

const ACTIVITY_MAX: f64 = 1e308;
const NULL_CLAUSE: ClauseId = ClauseId { ordinal: 0 };

impl Default for ClauseId {
    #[inline]
    /// return the default empty clause, used in a reason slot or no conflict path.
    fn default() -> Self {
        NULL_CLAUSE
    }
}

impl From<usize> for ClauseId {
    #[inline]
    fn from(u: usize) -> ClauseId {
        ClauseId { ordinal: u as u32 }
    }
}

impl fmt::Display for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if *self == ClauseId::default() {
            write!(f, "NullClause")
        } else {
            write!(f, "{}C", self.ordinal)
        }
    }
}

impl ClauseIdIF for ClauseId {
    /// return true if the clause is genereted from a literal by Eliminater.
    fn is_lifted_lit(self) -> bool {
        0 != 0x8000_0000 & self.ordinal
    }
}

/// 'watch literal' structure
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
    /// This O(n) functon is used only in Eliminator. So the cost can be ignored.
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

/// A representation of 'clause'
#[derive(Debug)]
pub struct Clause {
    /// The literals in a clause.
    pub lits: Vec<Lit>,
    /// A static clause evaluation criterion like LBD, NDD, or something.
    pub rank: usize,
    /// the ordinal of conflict at which this clause is checked.
    pub checked_at: usize,
    /// the index from which `propagate` starts seaching an unfalsified literal.
    pub search_from: usize,
    /// A dynamic clause evaluation criterion based on the number of references.
    reward: f64,
    /// Flags
    flags: Flag,
}

impl Default for Clause {
    fn default() -> Clause {
        Clause {
            lits: vec![],
            rank: 0,
            checked_at: 0,
            search_from: 2,
            reward: 0.0,
            flags: Flag::empty(),
        }
    }
}

impl Index<usize> for Clause {
    type Output = Lit;
    #[inline]
    fn index(&self, i: usize) -> &Lit {
        unsafe { self.lits.get_unchecked(i) }
    }
}

impl IndexMut<usize> for Clause {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Lit {
        unsafe { self.lits.get_unchecked_mut(i) }
    }
}

impl Index<Range<usize>> for Clause {
    type Output = [Lit];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Lit] {
        &self.lits[r]
    }
}

impl Index<RangeFrom<usize>> for Clause {
    type Output = [Lit];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Lit] {
        &self.lits[r]
    }
}

impl IndexMut<Range<usize>> for Clause {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Lit] {
        &mut self.lits[r]
    }
}

impl IndexMut<RangeFrom<usize>> for Clause {
    #[inline]
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
    fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }
    fn iter(&self) -> Iter<'_, Lit> {
        self.lits.iter()
    }
    fn len(&self) -> usize {
        self.lits.len()
    }
}

impl FlagIF for Clause {
    fn is(&self, flag: Flag) -> bool {
        self.flags.contains(flag)
    }
    fn set(&mut self, f: Flag, b: bool) {
        self.flags.set(f, b);
    }
    fn turn_off(&mut self, flag: Flag) {
        self.flags.remove(flag);
    }
    fn turn_on(&mut self, flag: Flag) {
        self.flags.insert(flag);
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Clause) -> bool {
        self == other
    }
}

impl Eq for Clause {}

impl PartialOrd for Clause {
    fn partial_cmp(&self, other: &Clause) -> Option<Ordering> {
        if self.rank < other.rank {
            Some(Ordering::Less)
        } else if other.rank < self.rank {
            Some(Ordering::Greater)
        } else if self.reward > other.reward {
            Some(Ordering::Less)
        } else if other.reward > self.reward {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl Ord for Clause {
    fn cmp(&self, other: &Clause) -> Ordering {
        if self.rank < other.rank {
            Ordering::Less
        } else if other.rank > self.rank {
            Ordering::Greater
        } else if self.reward > other.reward {
            Ordering::Less
        } else if other.reward > self.reward {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

impl Clause {
    #[allow(clippy::comparison_chain)]
    fn cmp_activity(&self, other: &Clause) -> Ordering {
        if self.reward > other.reward {
            Ordering::Less
        } else if other.reward > self.reward {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
    /// make a clause *dead*; the clause still exists in clause database as a garbage.
    fn kill(&mut self, touched: &mut [bool]) {
        self.turn_on(Flag::DEAD);
        debug_assert!(1 < usize::from(self.lits[0]) && 1 < usize::from(self.lits[1]));
        touched[!self.lits[0]] = true;
        touched[!self.lits[1]] = true;
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(
            f,
            "{{{:?}{}{}}}",
            vec2int(&self.lits),
            st(Flag::DEAD, ", dead"),
            st(Flag::ENQUEUED, ", enqueued"),
        )
    }
}

/// Clause database
///
///```
/// use crate::{splr::config::Config, splr::types::*};
/// use crate::splr::clause::ClauseDB;
/// let cdb = ClauseDB::instantiate(&Config::default(), &CNFDescription::default());
///```
#[derive(Debug)]
pub struct ClauseDB {
    /// container of clauses
    clause: Vec<Clause>,
    /// container of watch literals
    pub watcher: Vec<Vec<Watch>>,
    /// clause history to make certification
    pub certified: DRAT,
    /// a number of clauses to emit out-of-memory exception
    soft_limit: usize,
    /// flag for Chan Seok heuristics
    use_chan_seok: bool,
    /// 'small' clause threshold
    co_lbd_bound: usize,
    // not in use
    // lbd_frozen_clause: usize,

    //
    //## clause rewarding
    //
    activity_inc: f64,
    activity_decay: f64,

    //
    //## Elimination
    //
    /// dirty literals
    touched: Vec<bool>,

    //
    //## reduction
    //
    /// increment step of reduction threshold
    inc_step: usize,
    /// bonus step of reduction threshold used in good progress
    extra_inc: usize,
    first_reduction: usize,
    next_reduction: usize, // renamed from `nbclausesbeforereduce`
    reducable: bool,
    /// an expansion coefficient for restart
    reduction_coeff: usize,

    //
    //## statistics
    //
    /// the number of active (not DEAD) clauses.
    num_active: usize,
    /// the number of binary clauses.
    num_bi_clause: usize,
    /// the number of binary learnt clauses.
    num_bi_learnt: usize,
    /// the number of clauses which LBDs are 2.
    num_lbd2: usize,
    /// the present number of learnt clauses.
    num_learnt: usize,
    /// the number of reductions.
    num_reduction: usize,
}

impl Default for ClauseDB {
    fn default() -> ClauseDB {
        ClauseDB {
            clause: Vec::new(),
            watcher: Vec::new(),
            certified: Vec::new(),
            soft_limit: 0, // 248_000_000
            use_chan_seok: false,
            co_lbd_bound: 5,
            // lbd_frozen_clause: 30,
            activity_inc: 1.0,
            activity_decay: 0.999,
            touched: Vec::new(),
            inc_step: 300,
            extra_inc: 1000,
            first_reduction: 1000,
            next_reduction: 1000,
            reducable: true,
            reduction_coeff: 1,
            num_active: 0,
            num_bi_clause: 0,
            num_bi_learnt: 0,
            num_lbd2: 0,
            num_learnt: 0,
            num_reduction: 0,
        }
    }
}

impl Index<ClauseId> for ClauseDB {
    type Output = Clause;
    #[inline]
    fn index(&self, cid: ClauseId) -> &Clause {
        unsafe { self.clause.get_unchecked(cid.ordinal as usize) }
    }
}

impl IndexMut<ClauseId> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, cid: ClauseId) -> &mut Clause {
        unsafe { self.clause.get_unchecked_mut(cid.ordinal as usize) }
    }
}

impl Index<&ClauseId> for ClauseDB {
    type Output = Clause;
    #[inline]
    fn index(&self, cid: &ClauseId) -> &Clause {
        unsafe { self.clause.get_unchecked(cid.ordinal as usize) }
    }
}

impl IndexMut<&ClauseId> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, cid: &ClauseId) -> &mut Clause {
        unsafe { self.clause.get_unchecked_mut(cid.ordinal as usize) }
    }
}

impl Index<Range<usize>> for ClauseDB {
    type Output = [Clause];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Clause] {
        &self.clause[r]
    }
}

impl Index<RangeFrom<usize>> for ClauseDB {
    type Output = [Clause];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Clause] {
        &self.clause[r]
    }
}

impl IndexMut<Range<usize>> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Clause] {
        &mut self.clause[r]
    }
}

impl IndexMut<RangeFrom<usize>> for ClauseDB {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Clause] {
        &mut self.clause[r]
    }
}

impl ActivityIF for ClauseDB {
    type Ix = ClauseId;
    type Inc = ();
    fn activity(&mut self, ci: Self::Ix) -> f64 {
        self[ci].reward
    }
    fn bump_activity(&mut self, cid: Self::Ix, _: Self::Inc) {
        let c = &mut self.clause[cid.ordinal as usize];
        let a = c.reward + self.activity_inc;
        c.reward = a;
        if ACTIVITY_MAX < a {
            let scale = 1.0 / self.activity_inc;
            for c in &mut self.clause[1..] {
                if c.is(Flag::LEARNT) {
                    c.reward *= scale;
                }
            }
            self.activity_inc *= scale;
        }
    }
    fn scale_activity(&mut self) {
        self.activity_inc /= self.activity_decay;
    }
}

impl Instantiate for ClauseDB {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> ClauseDB {
        let nv = cnf.num_of_variables;
        let nc = cnf.num_of_clauses;
        let mut clause = Vec::with_capacity(1 + nc);
        clause.push(Clause::default());
        let mut watcher = Vec::with_capacity(2 * (nv + 1));
        let mut touched = Vec::with_capacity(2 * (nv + 1));
        for _ in 0..2 * (nv + 1) {
            watcher.push(Vec::new());
            touched.push(false);
        }
        let mut certified = Vec::new();
        if config.use_certification {
            certified.push((CertifiedRecord::SENTINEL, Vec::new()));
        }
        ClauseDB {
            clause,
            touched,
            watcher,
            certified,
            reducable: !config.without_reduce,
            soft_limit: config.clause_limit,
            ..ClauseDB::default()
        }
    }
    /// # PRECONDITION
    /// decision level must be 0 if `state.strategy.1` == `state[Stat::Conflict]`
    fn adapt_to(&mut self, state: &State, num_conflict: usize) {
        match state.strategy {
            (_, n) if n != num_conflict => (),
            (SearchStrategy::Initial, _) => (),
            (SearchStrategy::Generic, _) => (),
            (SearchStrategy::LowDecisions, _) => {
                self.co_lbd_bound = 4;
                self.reduction_coeff =
                    (num_conflict as f64 / self.next_reduction as f64 + 1.0) as usize;
                self.first_reduction = 2000;
                self.use_chan_seok = true;
                self.inc_step = 0;
                self.next_reduction = 2000;
                // This call requires 'decision level == 0'.
                self.make_permanent(true);
            }
            (SearchStrategy::HighSuccesive, _) => {
                self.co_lbd_bound = 3;
                self.first_reduction = 30000;
                self.use_chan_seok = true;
                // This call requires 'decision level == 0'.
                self.make_permanent(false);
            }
            (SearchStrategy::LowSuccesive, _) => (),
            (SearchStrategy::ManyGlues, _) => (),
        }
    }
}

impl Export<(usize, usize, usize, usize, usize, usize)> for ClauseDB {
    /// exports:
    ///  1. the number of active clauses
    ///  1. the number of binary clauses
    ///  1. the number of binary learnt clauses
    ///  1. the number of clauses which LBDs are 2
    ///  1. the number of learnt clauses
    ///  1. the number of clause reductions
    ///
    ///```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use crate::splr::clause::ClauseDB;
    /// let cdb = ClauseDB::instantiate(&Config::default(), &CNFDescription::default());
    /// let (_active, _bi_clause, _bi_learnt, _lbd2, _learnt, _reduction) = cdb.exports();
    ///```
    #[inline]
    fn exports(&self) -> (usize, usize, usize, usize, usize, usize) {
        (
            self.num_active,
            self.num_bi_clause,
            self.num_bi_learnt,
            self.num_lbd2,
            self.num_learnt,
            self.num_reduction,
        )
    }
}

impl ClauseDBIF for ClauseDB {
    fn len(&self) -> usize {
        self.clause.len()
    }
    fn is_empty(&self) -> bool {
        self.clause.is_empty()
    }
    fn iter(&self) -> Iter<'_, Clause> {
        self.clause.iter()
    }
    fn iter_mut(&mut self) -> IterMut<'_, Clause> {
        self.clause.iter_mut()
    }
    #[inline]
    fn watcher_list(&self, l: Lit) -> &[Watch] {
        &self.watcher[l]
    }
    #[inline]
    fn watcher_lists_mut(&mut self) -> &mut [Vec<Watch>] {
        &mut self.watcher
    }
    fn garbage_collect(&mut self) {
        // debug_assert!(self.check_liveness1());
        let ClauseDB {
            ref mut watcher,
            ref mut clause,
            ref mut touched,
            ref mut certified,
            ..
        } = self;
        debug_assert_eq!(usize::from(!NULL_LIT), 1);
        let (recycles, wss) = watcher.split_at_mut(2);
        let recycled = &mut recycles[1];
        for (i, ws) in &mut wss.iter_mut().enumerate() {
            if !touched[i + 2] {
                continue;
            }
            touched[i + 2] = false;
            let mut n = 0;
            while n < ws.len() {
                let cid = ws[n].c;
                let c = &mut clause[cid.ordinal as usize];
                if !c.is(Flag::DEAD) {
                    n += 1;
                    continue;
                }
                if !c.lits.is_empty() {
                    debug_assert!(c.is(Flag::DEAD));
                    recycled.push(Watch {
                        blocker: NULL_LIT,
                        c: cid,
                        binary: c.lits.len() == 2,
                    });
                    if c.is(Flag::LEARNT) {
                        self.num_learnt -= 1;
                    }
                    if !certified.is_empty() {
                        let temp = c.lits.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
                        certified.push((CertifiedRecord::ADD, temp));
                    }
                    c.lits.clear();
                }
                ws.detach(n);
            }
        }
        self.num_active = self.clause.len() - recycled.len();
        // debug_assert!(self.check_liveness2());
    }
    fn new_clause<A, V>(
        &mut self,
        asgs: &mut A,
        vec: &mut [Lit],
        level_sort: Option<&mut V>,
    ) -> ClauseId
    where
        A: AssignIF,
        V: VarDBIF,
    {
        let reward = self.activity_inc;
        let (rank, learnt) = if let Some(vdb) = level_sort {
            if !self.certified.is_empty() {
                let temp = vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
                self.certified.push((CertifiedRecord::ADD, temp));
            }
            #[cfg(feature = "boundary_check")]
            debug_assert!(1 < vec.len());
            let mut i_max = 1;
            let mut lv_max = 0;
            // seek a literal with max level
            let level = asgs.level_ref();
            for (i, l) in vec.iter().enumerate() {
                let vi = l.vi();
                let lv = level[vi];
                if vdb[vi].assign.is_some() && lv_max < lv {
                    i_max = i;
                    lv_max = lv;
                }
            }
            vec.swap(1, i_max);
            if vec.len() <= 2 {
                (0, false)
            } else {
                let lbd = asgs.compute_lbd(vec);
                if self.use_chan_seok && lbd <= self.co_lbd_bound {
                    (0, false)
                } else {
                    (lbd, true)
                }
            }
        } else {
            (0, false)
        };
        let cid;
        let l0 = vec[0];
        let l1 = vec[1];
        if let Some(w) = self.watcher[!NULL_LIT].pop() {
            cid = w.c;
            let c = &mut self[cid];
            // if !c.is(Flag::DEAD) {
            //     println!("{} {:?}", cid.format(), vec2int(&c.lits));
            //     println!("len {}", self.watcher[NULL_LIT.negate() as usize].len());
            //     for w in &self.watcher[NULL_LIT.negate() as usize][..10] {
            //         if !self.clause[w.c].is(Flag::DEAD) {
            //             println!("{}", w.c.format());
            //         }
            //     }
            //     panic!("done");
            // }
            debug_assert!(c.is(Flag::DEAD));
            c.flags = Flag::empty();
            c.lits.clear();
            for l in vec {
                c.lits.push(*l);
            }
            c.rank = rank;
            c.reward = reward;
            c.checked_at = 0;
            c.search_from = 2;
        } else {
            let mut lits = Vec::with_capacity(vec.len());
            for l in vec {
                lits.push(*l);
            }
            cid = ClauseId::from(self.clause.len());
            let c = Clause {
                flags: Flag::empty(),
                lits,
                rank,
                reward,
                ..Clause::default()
            };
            self.clause.push(c);
        };
        let c = &mut self[cid];
        let len2 = c.lits.len() == 2;
        if learnt {
            c.turn_on(Flag::LEARNT);
            c.turn_on(Flag::JUST_USED);

            let lbd2 = c.rank <= 2;
            if len2 {
                self.num_bi_learnt += 1;
            }
            if lbd2 {
                self.num_lbd2 += 1;
            }
            self.num_learnt += 1;
        }
        if len2 {
            self.num_bi_clause += 1;
        }
        self.watcher[!l0].register(l1, cid, len2);
        self.watcher[!l1].register(l0, cid, len2);
        self.num_active += 1;
        cid
    }
    fn convert_to_permanent<A>(&mut self, asgs: &mut A, cid: ClauseId) -> bool
    where
        A: AssignIF,
    {
        let chan_seok_condition = if self.use_chan_seok {
            self.co_lbd_bound
        } else {
            0
        };
        let c = &mut self[cid];
        if c.is(Flag::JUST_USED) {
            return false;
        }
        debug_assert!(!c.is(Flag::DEAD), format!("found {} is dead: {}", cid, c));
        if 2 < c.rank {
            c.turn_on(Flag::JUST_USED);
            let nlevels = asgs.compute_lbd(&c.lits);
            if nlevels + 1 < c.rank {
                // chan_seok_condition is zero if !use_chan_seok
                if nlevels < chan_seok_condition {
                    c.turn_off(Flag::LEARNT);
                    self.num_learnt -= 1;
                    return true;
                } else {
                    c.rank = nlevels;
                }
            }
        }
        false
    }
    fn count(&self, alive: bool) -> usize {
        if alive {
            self.clause.len() - self.watcher[!NULL_LIT].len() - 1
        } else {
            self.clause.len() - 1
        }
    }
    fn countf(&self, mask: Flag) -> usize {
        self.clause
            .iter()
            .skip(1)
            .filter(|&c| c.flags.contains(mask) && !c.flags.contains(Flag::DEAD))
            .count()
    }
    /// ## Warning
    /// this function is the only function that turns `Flag::DEAD` on without calling
    /// `garbage_collect` which erases all the `DEAD` flags. So you must care about how and when
    /// `garbage_collect` is called.
    fn detach(&mut self, cid: ClauseId) {
        let c = &mut self.clause[cid.ordinal as usize];
        debug_assert!(!c.is(Flag::DEAD));
        debug_assert!(1 < c.lits.len());
        c.kill(&mut self.touched);
    }
    fn check_and_reduce<V>(&mut self, vdb: &mut V, nc: usize) -> bool
    where
        V: VarDBIF,
    {
        if !self.reducable || 0 == self.num_learnt {
            return false;
        }
        let go = if self.use_chan_seok {
            self.first_reduction < self.num_learnt
        } else {
            self.reduction_coeff * self.next_reduction <= nc
        };
        if go {
            self.reduction_coeff = ((nc as f64) / (self.next_reduction as f64)) as usize + 1;
            self.reduce(vdb);
            self.num_reduction += 1;
        }
        go
    }
    fn reset(&mut self) {
        debug_assert!(1 < self.clause.len());
        for c in &mut self.clause[1..] {
            if c.is(Flag::LEARNT) && !c.is(Flag::DEAD) && self.co_lbd_bound < c.lits.len() {
                c.kill(&mut self.touched);
            }
        }
        self.garbage_collect();
    }
    fn certificate_add(&mut self, vec: &[Lit]) {
        if !self.certified.is_empty() {
            let temp = vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
            self.certified.push((CertifiedRecord::ADD, temp));
        }
    }
    fn certificate_delete(&mut self, vec: &[Lit]) {
        if !self.certified.is_empty() {
            let temp = vec.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
            self.certified.push((CertifiedRecord::DELETE, temp));
        }
    }
    fn eliminate_satisfied_clauses<E, V>(&mut self, elim: &mut E, vdb: &mut V, update_occur: bool)
    where
        E: EliminateIF,
        V: VarDBIF,
    {
        for (cid, c) in &mut self.clause.iter_mut().enumerate().skip(1) {
            if !c.is(Flag::DEAD) && vdb.satisfies(&c.lits) {
                c.kill(&mut self.touched);
                if elim.is_running() {
                    if update_occur {
                        elim.remove_cid_occur(vdb, ClauseId::from(cid), c);
                    }
                    for l in &c.lits {
                        elim.enqueue_var(vdb, l.vi(), true);
                    }
                }
            }
        }
        self.garbage_collect();
    }
    fn touch_var(&mut self, vi: VarId) {
        self.touched[Lit::from_assign(vi, true)] = true;
        self.touched[Lit::from_assign(vi, false)] = true;
    }
    fn check_size(&self) -> Result<bool, SolverError> {
        if self.soft_limit == 0 || self.count(false) <= self.soft_limit {
            Ok(0 == self.soft_limit || 4 * self.count(true) < 3 * self.soft_limit)
        } else {
            Err(SolverError::OutOfMemory)
        }
    }
    fn validate<V>(&self, vdb: &V, strict: bool) -> Option<ClauseId>
    where
        V: VarDBIF,
    {
        for (i, c) in self.clause.iter().enumerate().skip(1) {
            if c.is(Flag::DEAD) || (strict && c.is(Flag::LEARNT)) {
                continue;
            }
            match vdb.status(&c.lits) {
                Some(false) => return Some(ClauseId::from(i)),
                None if strict => return Some(ClauseId::from(i)),
                _ => (),
            }
        }
        None
    }
    fn strengthen(&mut self, cid: ClauseId, p: Lit) -> bool {
        debug_assert!(!self[cid].is(Flag::DEAD));
        debug_assert!(1 < self[cid].len());
        let c = &mut self[cid];
        // debug_assert!((*ch).lits.contains(&p));
        // debug_assert!(1 < (*ch).len());
        if (*c).is(Flag::DEAD) {
            return false;
        }
        (*c).turn_on(Flag::JUST_USED);
        debug_assert!(1 < usize::from(!p));
        let lits = &mut (*c).lits;
        debug_assert!(1 < lits.len());
        if lits.len() == 2 {
            if lits[0] == p {
                lits.swap(0, 1);
            }
            debug_assert!(1 < usize::from(!lits[0]));
            return true;
        }
        if lits[0] == p || lits[1] == p {
            let (q, r) = if lits[0] == p {
                lits.swap_remove(0);
                (lits[0], lits[1])
            } else {
                lits.swap_remove(1);
                (lits[1], lits[0])
            };
            debug_assert!(1 < usize::from(!p));
            let len = lits.len();
            let bin = len == 2;
            self.watcher[!p].detach_with(cid);
            self.watcher[!q].register(r, cid, bin);
            if bin {
                // update another bocker
                self.watcher[!r].update_blocker(cid, q, true);
            }
        } else {
            lits.delete_unstable(|&x| x == p);
            if lits.len() == 2 {
                // update another bocker
                let q = lits[0];
                let r = lits[1];
                self.watcher[!q].update_blocker(cid, r, true);
                self.watcher[!r].update_blocker(cid, q, true);
            }
        }
        false
    }
}

impl ClauseDB {
    /// halve the number of 'learnt' or *removable* clauses.
    fn reduce<V>(&mut self, vdb: &mut V)
    where
        V: VarDBIF,
    {
        let ClauseDB {
            ref mut clause,
            ref mut touched,
            ..
        } = self;
        self.next_reduction += self.inc_step;
        let mut perm = Vec::with_capacity(clause.len());
        for (i, c) in clause.iter_mut().enumerate().skip(1) {
            let used = c.is(Flag::JUST_USED);
            if c.is(Flag::LEARNT) && !c.is(Flag::DEAD) && !vdb.locked(c, ClauseId::from(i)) && !used
            {
                perm.push(i);
            }
            if used {
                c.turn_off(Flag::JUST_USED)
            }
        }
        if perm.is_empty() {
            return;
        }
        let keep = perm.len() / 2;
        if self.use_chan_seok {
            perm.sort_by(|&a, &b| clause[a].cmp_activity(&clause[b]));
        } else {
            perm.sort_by(|&a, &b| clause[a].cmp(&clause[b]));
            if clause[perm[keep]].rank <= 3 {
                self.next_reduction += self.extra_inc;
            }
            if clause[perm[0]].rank <= 5 {
                self.next_reduction += self.extra_inc;
            };
        }
        for i in &perm[keep..] {
            let c = &mut clause[*i];
            if 2 < c.rank {
                c.kill(touched);
            }
        }
        debug_assert!(perm[0..keep].iter().all(|cid| !clause[*cid].is(Flag::DEAD)));
        self.garbage_collect();
    }
    /// change good learnt clauses to permanent one.
    fn make_permanent(&mut self, reinit: bool) {
        // Adjusting for low decision levels.
        // move some clauses with good LBDs (col_lbd_bound) to Permanent
        for c in &mut self.clause[1..] {
            if c.is(Flag::DEAD) || !c.is(Flag::LEARNT) {
                continue;
            }
            if c.rank <= self.co_lbd_bound {
                c.turn_off(Flag::LEARNT);
                self.num_learnt -= 1;
            } else if reinit {
                c.kill(&mut self.touched);
            }
        }
        self.garbage_collect();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assign::{AssignIF, AssignStack};
    use crate::clause::ClauseDB;
    use crate::var::VarDB;

    fn lit(i: i32) -> Lit {
        Lit::from(i)
    }

    #[allow(dead_code)]
    fn check_watches(cdb: &ClauseDB, cid: ClauseId) {
        let c = &cdb.clause[cid.ordinal as usize];
        if c.lits.is_empty() {
            println!("skip checking watches of an empty clause");
            return;
        }
        for l in &c.lits[0..=1] {
            let ws = &cdb.watcher[!*l];
            assert!(ws.iter().any(|w| w.c == cid));
        }
        println!("pass to check watches");
    }

    #[test]
    fn test_clause_instanciation() -> () {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asgs = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let mut vdb = VarDB::instantiate(&config, &cnf);
        asgs.assign_by_decision(&mut vdb, lit(1));
        asgs.assign_by_decision(&mut vdb, lit(-2));

        let c1 = cdb.new_clause(&mut asgs, &mut [lit(1), lit(2), lit(3)], None::<&mut VarDB>);
        let c = &cdb[c1];
        assert_eq!(c.rank, 0);
        assert!(!c.is(Flag::DEAD));
        assert!(!c.is(Flag::LEARNT));
        assert!(!c.is(Flag::JUST_USED));

        let c2 = cdb.new_clause(&mut asgs, &mut [lit(-1), lit(2), lit(3)], Some(&mut vdb));
        let c = &cdb[c2];
        assert_eq!(c.rank, 2);
        assert!(!c.is(Flag::DEAD));
        assert!(c.is(Flag::LEARNT));
        assert!(c.is(Flag::JUST_USED));
    }
    #[test]
    fn test_clause_equality() -> () {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asgs = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let c1 = cdb.new_clause(&mut asgs, &mut [lit(1), lit(2), lit(3)], None::<&mut VarDB>);
        let c2 = cdb.new_clause(&mut asgs, &mut [lit(-1), lit(4)], None::<&mut VarDB>);
        cdb[c2].reward = 2.4;
        assert_eq!(c1, c1);
        assert_eq!(c1 == c1, true);
        assert_ne!(c1, c2);
        assert_eq!(cdb.activity(c2), 2.4);
    }

    #[test]
    fn test_clause_iterator() -> () {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut asgs = AssignStack::instantiate(&config, &cnf);
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let c1 = cdb.new_clause(&mut asgs, &mut [lit(1), lit(2), lit(3)], None::<&mut VarDB>);
        assert_eq!(cdb[c1][0..].iter().map(|l| i32::from(*l)).sum::<i32>(), 6);
        let mut iter = cdb[c1][0..].into_iter();
        assert_eq!(iter.next(), Some(&lit(1)));
        assert_eq!(iter.next(), Some(&lit(2)));
        assert_eq!(iter.next(), Some(&lit(3)));
        assert_eq!(iter.next(), None);
    }
}

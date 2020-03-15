/// Crate `clause` provides `clause` object and its manager `ClauseDB`
use {
    crate::{
        config::Config,
        eliminator::{Eliminator, EliminatorIF},
        state::{ProgressComponent, SearchStrategy, Stat, State},
        types::*,
        var::{VarDB, VarDBIF, LBDIF},
    },
    std::{
        cmp::Ordering,
        fmt,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::Iter,
    },
};

/// API for Clause, providing `kill`.
pub trait ClauseIF {
    /// return true if it contains no literals; a clause after unit propagation.
    fn is_empty(&self) -> bool;
    /// return an iterator over its literals.
    fn iter(&self) -> Iter<'_, Lit>;
    /// return the number of literals.
    fn len(&self) -> usize;
}

/// API for clause management like `reduce`, `simplify`, `new_clause`, and so on.
pub trait ClauseDBIF {
    /// return the length of `clause`.
    fn len(&self) -> usize;
    /// return true if it's empty.
    fn is_empty(&self) -> bool;
    /// make a new clause from `state.new_learnt` and register it to clause database.
    fn attach(&mut self, v: &mut [Lit], vdb: &mut VarDB, lbd: usize) -> ClauseId;
    /// unregister a clause `cid` from clause database and make the clause dead.
    fn detach(&mut self, cid: ClauseId);
    /// check a condition to reduce.
    fn check_and_reduce(&mut self, vdb: &mut VarDB, nc: usize) -> bool;
    fn reset(&mut self);
    /// delete *dead* clauses from database, which are made by:
    /// * `reduce`
    /// * `simplify`
    /// * `kill`
    fn garbage_collect(&mut self);
    /// allocate a new clause and return its id.
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool) -> ClauseId;
    /// return the number of alive clauses in the database. Or return the database size if `active` is `false`.
    fn count(&self, alive: bool) -> usize;
    /// return the number of clauses which satisfy given flags and aren't DEAD.
    fn countf(&self, mask: Flag) -> usize;
    /// record a clause to unsat certification.
    fn certificate_add(&mut self, vec: &[Lit]);
    /// record a deleted clause to unsat certification.
    fn certificate_delete(&mut self, vec: &[Lit]);
    /// delete satisfied clauses at decision level zero.
    fn eliminate_satisfied_clauses(&mut self, elim: &mut Eliminator, vdb: &mut VarDB, occur: bool);
    /// flag positive and negative literals of a var as dirty
    fn touch_var(&mut self, vi: VarId);
    /// return LBD threshold used in glue reduciton mode.
    fn chan_seok_condition(&self) -> usize;
    /// emit an error if the db size (the number of clauses) is over the limit.
    fn check_size(&self) -> MaybeInconsistent;
    /// returns None if the given assignment is a model of a problem.
    /// Otherwise returns a clause which is not satisfiable under a given assignment.
    /// Clauses with an unassigned literal are treated as falsified in `strict` mode.
    fn validate(&self, vdb: &VarDB, strict: bool) -> Option<ClauseId>;
}

/// API for Clause Id.
pub trait ClauseIdIF {
    /// return `true` if a given clause id is made from a `Lit`.
    fn is_lifted_lit(self) -> bool;
}

/// API for 'watcher list' like `attach`, `detach`, `detach_with` and so on.
pub trait WatchDBIF {
    /// make a new 'watch', and add it to this watcher list.
    fn register(&mut self, blocker: Lit, c: ClauseId);
    /// remove *n*-th clause from the watcher list. *O(1)* operation.
    fn detach(&mut self, n: usize);
    /// remove a clause which id is `cid` from the watcher list. *O(n)* operation.
    fn detach_with(&mut self, cid: ClauseId);
    /// update blocker of cid.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit);
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
            write!(f, "CID{}", self.ordinal)
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
    fn register(&mut self, blocker: Lit, c: ClauseId) {
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
    }
    /// This O(n) functon is used only in Eliminator. So the cost can be ignore.
    fn update_blocker(&mut self, cid: ClauseId, l: Lit) {
        for w in &mut self[..] {
            if w.c == cid {
                w.blocker = l;
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
            "C{{{:?} {}{}}}",
            vec2int(&self.lits),
            st(Flag::DEAD, ", dead"),
            st(Flag::ENQUEUED, ", enqueued"),
        )
    }
}

/// Clause database
#[derive(Debug)]
pub struct ClauseDB {
    /// container of clauses
    clause: Vec<Clause>,
    /// container of watch literals
    pub watcher: Vec<Vec<Watch>>,
    /// the present number of learnt clauses
    pub num_learnt: usize,
    num_active: usize,
    /// clause history to make certification
    pub certified: DRAT,
    /// a number of clauses to emit out-of-memory exception
    pub soft_limit: usize,
    /// flag for Chan Seok heuristics
    use_chan_seok: bool,
    /// 'small' clause threshold
    co_lbd_bound: usize,
    // not in use
    // lbd_frozen_clause: usize,

    //[clause rewarding]
    activity_inc: f64,
    activity_decay: f64,

    //[Elimination]
    /// dirty literals
    touched: Vec<bool>,

    //[reduction]
    // increment step of reduction threshold
    inc_step: usize,
    // bonus step of reduction threshold used in good progress
    extra_inc: usize,
    first_reduction: usize,
    next_reduction: usize, // renamed from `nbclausesbeforereduce`
    // an expansion coefficient for restart
    reduction_coeff: usize,
}

impl Default for ClauseDB {
    fn default() -> ClauseDB {
        ClauseDB {
            clause: Vec::new(),
            watcher: Vec::new(),
            num_active: 0,
            num_learnt: 0,
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
            reduction_coeff: 1,
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
            soft_limit: config.clause_limit,
            ..ClauseDB::default()
        }
    }
    fn adapt_to(&mut self, state: &State) {
        match state.strategy {
            (_, n) if n != state[Stat::Conflict] => (),
            (SearchStrategy::Initial, _) => (),
            (SearchStrategy::Generic, _) => (),
            (SearchStrategy::LowDecisions, _) => {
                let nc = state[Stat::Conflict];
                self.co_lbd_bound = 4;
                self.reduction_coeff = (nc as f64 / self.next_reduction as f64 + 1.0) as usize;
                self.first_reduction = 2000;
                self.use_chan_seok = true;
                self.inc_step = 0;
                self.next_reduction = 2000;
                self.make_permanent(true);
            }
            (SearchStrategy::HighSuccesive, _) => {
                self.co_lbd_bound = 3;
                self.first_reduction = 30000;
                self.use_chan_seok = true;
                self.make_permanent(false);
            }
            (SearchStrategy::LowSuccesiveLuby, _) => (),
            (SearchStrategy::LowSuccesiveM, _) => (),
            (SearchStrategy::ManyGlues, _) => (),
        }
    }
}

impl ClauseDBIF for ClauseDB {
    fn len(&self) -> usize {
        self.clause.len()
    }
    fn is_empty(&self) -> bool {
        self.clause.is_empty()
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
    fn new_clause(&mut self, v: &[Lit], rank: usize, learnt: bool) -> ClauseId {
        let cid;
        let l0 = v[0];
        let l1 = v[1];
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
            for l in v {
                c.lits.push(*l);
            }
            c.rank = rank;
            c.reward = 0.0;
        } else {
            let mut lits = Vec::with_capacity(v.len());
            for l in v {
                lits.push(*l);
            }
            cid = ClauseId::from(self.clause.len());
            let c = Clause {
                flags: Flag::empty(),
                lits,
                rank,
                reward: 0.0,
            };
            self.clause.push(c);
        };
        let c = &mut self[cid];
        if learnt {
            c.turn_on(Flag::LEARNT);
            self.num_learnt += 1;
        }
        self.watcher[!l0].register(l1, cid);
        self.watcher[!l1].register(l0, cid);
        self.num_active += 1;
        cid
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
    // Note: set LBD to 0 if you want to add the clause to Permanent.
    fn attach(&mut self, v: &mut [Lit], vdb: &mut VarDB, lbd: usize) -> ClauseId {
        if !self.certified.is_empty() {
            let temp = v.iter().map(|l| i32::from(*l)).collect::<Vec<_>>();
            self.certified.push((CertifiedRecord::ADD, temp));
        }
        debug_assert!(1 < v.len());
        let mut i_max = 1;
        let mut lv_max = 0;
        // seek a literal with max level
        for (i, l) in v.iter().enumerate() {
            let vi = l.vi();
            let lv = vdb[vi].level;
            if vdb[vi].assign.is_some() && lv_max < lv {
                i_max = i;
                lv_max = lv;
            }
        }
        v.swap(1, i_max);
        let learnt = 0 < lbd && 2 < v.len() && (!self.use_chan_seok || self.co_lbd_bound < lbd);
        let cid = self.new_clause(&v, lbd, learnt);
        let c = &mut self.clause[cid.ordinal as usize];
        c.reward = self.activity_inc;
        cid
    }
    fn detach(&mut self, cid: ClauseId) {
        let c = &mut self.clause[cid.ordinal as usize];
        debug_assert!(!c.is(Flag::DEAD));
        debug_assert!(1 < c.lits.len());
        c.kill(&mut self.touched);
    }
    fn check_and_reduce(&mut self, vdb: &mut VarDB, nc: usize) -> bool {
        if 0 == self.num_learnt {
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
    fn eliminate_satisfied_clauses(
        &mut self,
        elim: &mut Eliminator,
        vdb: &mut VarDB,
        update_occur: bool,
    ) {
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
    }
    fn touch_var(&mut self, vi: VarId) {
        self.touched[Lit::from_assign(vi, true)] = true;
        self.touched[Lit::from_assign(vi, false)] = true;
    }
    fn chan_seok_condition(&self) -> usize {
        if self.use_chan_seok {
            self.co_lbd_bound
        } else {
            0
        }
    }
    fn check_size(&self) -> MaybeInconsistent {
        if self.soft_limit == 0 || self.count(false) <= self.soft_limit {
            Ok(())
        } else {
            Err(SolverError::OutOfMemory)
        }
    }
    fn validate(&self, vdb: &VarDB, strict: bool) -> Option<ClauseId> {
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
}

impl ProgressComponent for ClauseDB {
    type Output = (usize, usize);
    fn progress_component(&self) -> Self::Output {
        (self.num_active, self.num_learnt)
    }
}

impl ClauseDB {
    /// halve the number of 'learnt' or *removable* clauses.
    fn reduce(&mut self, vdb: &mut VarDB) {
        vdb.reset_lbd(self);
        let ClauseDB {
            ref mut clause,
            ref mut touched,
            ..
        } = self;
        self.next_reduction += self.inc_step;
        let mut perm = Vec::with_capacity(clause.len());
        for (i, b) in clause.iter().enumerate().skip(1) {
            if b.is(Flag::LEARNT) && !b.is(Flag::DEAD) && !vdb.locked(b, ClauseId::from(i)) {
                perm.push(i);
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
            // if c.is(Flag::JUST_USED) {
            //     c.turn_off(Flag::JUST_USED)
            // }
            if 2 < c.rank {
                c.kill(touched);
            }
        }
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

    fn lit(i: i32) -> Lit {
        Lit::from(i)
    }

    #[test]
    fn test_clause_equality() -> () {
        let config = Config::default();
        let cnf = CNFDescription {
            num_of_variables: 4,
            ..CNFDescription::default()
        };
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let c1 = cdb.new_clause(&[lit(1), lit(2), lit(3)], 0, false);
        let c2 = cdb.new_clause(&[lit(-1), lit(4)], 0, false);
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
        let mut cdb = ClauseDB::instantiate(&config, &cnf);
        let c1 = cdb.new_clause(&[lit(1), lit(2), lit(3)], 0, false);
        assert_eq!(cdb[c1][0..].iter().map(|l| i32::from(*l)).sum::<i32>(), 6);
        let mut iter = cdb[c1][0..].into_iter();
        assert_eq!(iter.next(), Some(&lit(1)));
        assert_eq!(iter.next(), Some(&lit(2)));
        assert_eq!(iter.next(), Some(&lit(3)));
        assert_eq!(iter.next(), None);
    }
}

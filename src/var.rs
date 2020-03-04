/// Crate `var` provides `var` object and its manager `VarDB`.
use {
    crate::{
        clause::{Clause, ClauseDB, ClauseIF, ClauseId, ClauseIdIF},
        config::Config,
        propagator::{AssignStack, PropagatorIF},
        state::SearchStrategy,
        types::*,
    },
    std::{
        fmt,
        ops::{Index, IndexMut, Range, RangeFrom},
        slice::Iter,
    },
};

/// API to calculate LBD.
pub trait LBDIF {
    /// return the LBD value for a set of literals.
    fn compute_lbd(&mut self, vec: &[Lit]) -> usize;
    /// re-calculate the LBD values of all (learnt) clauses.
    fn reset_lbd(&mut self, cdb: &mut ClauseDB);
}

/// API for var DB like `assigned`, `locked`, and so on.
pub trait VarDBIF {
    /// return the number of vars.
    fn len(&self) -> usize;
    /// return true if it's empty.
    fn is_empty(&self) -> bool;
    /// return an interator over vars.
    fn iter(&self) -> Iter<'_, Var>;
    /// return the 'value' of a given literal.
    fn assigned(&self, l: Lit) -> Option<bool>;
    /// return `true` is the clause is the reason of the assignment.
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool;
    /// return `true` if the set of literals is satisfiable under the current assignment.
    fn satisfies(&self, c: &[Lit]) -> bool;
    /// return Option<bool>
    /// - Some(true) -- the literals is satisfied by a literal
    /// - Some(false) -- the literals is unsatisfied; no unassigned literal
    /// - None -- the literals contains an unassigned literal
    fn status(&self, c: &[Lit]) -> Option<bool>;
    /// set up parameters for each SearchStrategy.
    fn adapt_strategy(&mut self, mode: &SearchStrategy, elapsed: f64);
    /// minimize a clause.
    fn minimize_with_biclauses(&mut self, cdb: &ClauseDB, vec: &mut Vec<Lit>);
}

/// API for var rewarding.
pub trait VarRewardIF {
    /// return var's activity.
    fn activity(&mut self, vi: VarId) -> f64;
    /// initialize rewards based on an order of vars.
    fn initialize_reward(&mut self, iterator: Iter<'_, usize>);
    /// modify var's activity at conflict analysis in `analyze`.
    fn reward_at_analysis(&mut self, vi: VarId);
    /// modify var's activity at value assignment in `uncheck_{assume, enquue, fix}`.
    fn reward_at_assign(&mut self, vi: VarId);
    /// modify var's activity at value unassigment in `cancel_until`.
    fn reward_at_unassign(&mut self, vi: VarId);
    /// update internal counter.
    fn reward_update(&mut self);
}

/// Object representing a variable.
#[derive(Debug)]
pub struct Var {
    /// reverse conversion to index. Note `VarId` must be `usize`.
    pub index: VarId,
    /// the current value.
    pub assign: Option<bool>,
    /// the propagating clause
    pub reason: ClauseId,
    /// decision level at which this variables is assigned.
    pub level: usize,
    /// the number of participation in conflict analysis
    participated: usize,
    /// a dynamic evaluation criterion like VSIDS or ACID.
    reward: f64,
    /// the number of conflicts at which this var was assigned lastly.
    timestamp: usize,
    /// the `Flag`s
    flags: Flag,
}

impl Default for Var {
    fn default() -> Var {
        Var {
            index: 0,
            assign: None,
            reason: ClauseId::default(),
            level: 0,
            reward: 0.0,
            timestamp: 0,
            flags: Flag::empty(),
            participated: 0,
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(
            f,
            "V{}({:?} at {} by {} {}{})",
            self.index,
            self.assign,
            self.level,
            self.reason.format(),
            st(Flag::TOUCHED, ", touched"),
            st(Flag::ELIMINATED, ", eliminated"),
        )
    }
}

impl From<usize> for Var {
    #[inline]
    fn from(i: usize) -> Self {
        Var {
            index: i,
            ..Var::default()
        }
    }
}

impl Var {
    /// return a new vector of $n$ `Var`s.
    fn new_vars(n: usize) -> Vec<Var> {
        let mut vec = Vec::with_capacity(n + 1);
        for i in 0..=n {
            vec.push(Var::from(i));
        }
        vec
    }
    fn assigned(&self, l: Lit) -> Option<bool> {
        match self.assign {
            Some(x) if !bool::from(l) => Some(!x),
            x => x,
        }
    }
}

impl FlagIF for Var {
    #[inline]
    fn is(&self, flag: Flag) -> bool {
        self.flags.contains(flag)
    }
    #[inline]
    fn set(&mut self, f: Flag, b: bool) {
        self.flags.set(f, b);
    }
    #[inline]
    fn turn_off(&mut self, flag: Flag) {
        self.flags.remove(flag);
    }
    #[inline]
    fn turn_on(&mut self, flag: Flag) {
        self.flags.insert(flag);
    }
}

#[derive(Clone, Copy, Eq, Debug, PartialEq, PartialOrd, Ord)]
pub enum RewardStep {
    HeatUp = 0,
    Annealing,
    Final,
    Fixed,
}

/// A container of variables.
#[derive(Debug)]
pub struct VarDB {
    /// var activity decay
    pub activity_decay: f64,
    /// an index for counting elapsed time
    ordinal: usize,
    /// vars
    var: Vec<Var>,
    /// a working buffer for LBD calculation
    lbd_temp: Vec<usize>,
}

impl Default for VarDB {
    fn default() -> VarDB {
        VarDB {
            activity_decay: 0.8,
            ordinal: 0,
            var: Vec::new(),
            lbd_temp: Vec::new(),
        }
    }
}

impl Index<VarId> for VarDB {
    type Output = Var;
    #[inline]
    fn index(&self, i: VarId) -> &Self::Output {
        unsafe { self.var.get_unchecked(i) }
    }
}

impl IndexMut<VarId> for VarDB {
    #[inline]
    fn index_mut(&mut self, i: VarId) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(i) }
    }
}

impl Index<&VarId> for VarDB {
    type Output = Var;
    #[inline]
    fn index(&self, i: &VarId) -> &Self::Output {
        unsafe { self.var.get_unchecked(*i) }
    }
}

impl IndexMut<&VarId> for VarDB {
    #[inline]
    fn index_mut(&mut self, i: &VarId) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(*i) }
    }
}

impl Index<Lit> for VarDB {
    type Output = Var;
    #[inline]
    fn index(&self, l: Lit) -> &Self::Output {
        unsafe { self.var.get_unchecked(l.vi()) }
    }
}

impl IndexMut<Lit> for VarDB {
    #[inline]
    fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(l.vi()) }
    }
}

impl Index<&Lit> for VarDB {
    type Output = Var;
    #[inline]
    fn index(&self, l: &Lit) -> &Self::Output {
        unsafe { self.var.get_unchecked(l.vi()) }
    }
}

impl IndexMut<&Lit> for VarDB {
    #[inline]
    fn index_mut(&mut self, l: &Lit) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(l.vi()) }
    }
}

impl Index<Range<usize>> for VarDB {
    type Output = [Var];
    #[inline]
    fn index(&self, r: Range<usize>) -> &Self::Output {
        &self.var[r]
    }
}

impl Index<RangeFrom<usize>> for VarDB {
    type Output = [Var];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &Self::Output {
        unsafe { self.var.get_unchecked(r) }
    }
}

impl IndexMut<Range<usize>> for VarDB {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut Self::Output {
        unsafe { self.var.get_unchecked_mut(r) }
    }
}

impl IndexMut<RangeFrom<usize>> for VarDB {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut Self::Output {
        &mut self.var[r]
    }
}

impl VarRewardIF for VarDB {
    #[inline]
    fn activity(&mut self, vi: VarId) -> f64 {
        self[vi].reward
    }
    fn initialize_reward(&mut self, iterator: Iter<'_, usize>) {
        let mut v = 0.5; // big bang initialization
        for vi in iterator {
            self.var[*vi].reward = v;
            v *= 0.9;
        }
    }
    fn reward_at_analysis(&mut self, vi: VarId) {
        let v = &mut self[vi];
        v.participated += 1;
    }
    fn reward_at_assign(&mut self, vi: VarId) {
        self[vi].timestamp = self.ordinal;
    }
    fn reward_at_unassign(&mut self, vi: VarId) {
        let v = &mut self.var[vi];
        let duration = self.ordinal + 1 - v.timestamp;
        let rate = v.participated as f64 / duration as f64;
        v.reward *= self.activity_decay;
        v.reward += (1.0 - self.activity_decay) * rate;
        v.participated = 0;
    }
    fn reward_update(&mut self) {
        self.ordinal += 1;
    }
}

impl Instantiate for VarDB {
    fn instantiate(_: &Config, cnf: &CNFDescription) -> Self {
        let nv = cnf.num_of_variables;
        VarDB {
            var: Var::new_vars(nv),
            lbd_temp: vec![0; nv + 1],
            ..VarDB::default()
        }
    }
}

impl VarDBIF for VarDB {
    fn len(&self) -> usize {
        self.var.len()
    }
    fn is_empty(&self) -> bool {
        self.var.is_empty()
    }
    fn iter(&self) -> Iter<'_, Var> {
        self.var.iter()
    }
    fn assigned(&self, l: Lit) -> Option<bool> {
        match unsafe { self.var.get_unchecked(l.vi()).assign } {
            Some(x) if !bool::from(l) => Some(!x),
            x => x,
        }
    }
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool {
        let lits = &c.lits;
        debug_assert!(1 < lits.len());
        let l0 = lits[0];
        self.assigned(l0) == Some(true) && self[l0.vi()].reason == cid
    }
    fn satisfies(&self, vec: &[Lit]) -> bool {
        for l in vec {
            if self.assigned(*l) == Some(true) {
                return true;
            }
        }
        false
    }
    fn status(&self, vec: &[Lit]) -> Option<bool> {
        let mut falsified = Some(false);
        for l in vec {
            match self.assigned(*l) {
                Some(true) => return Some(true),
                None => falsified = None,
                _ => (),
            }
        }
        falsified
    }
    fn adapt_strategy(&mut self, mode: &SearchStrategy, elapsed: f64) {
        self.activity_decay = (0.7 + 0.32 * elapsed.sqrt()).min(0.96);
        match mode {
            SearchStrategy::Initial => (),
            SearchStrategy::Generic => (),
            SearchStrategy::LowDecisions => {
                // self.fix_reward(0.96);
            }
            SearchStrategy::HighSuccesive => {
                // self.fix_reward(0.99);
            }
            SearchStrategy::LowSuccesiveLuby | SearchStrategy::LowSuccesiveM => {
                // self.fix_reward(0.999);
            }
            SearchStrategy::ManyGlues => {
                // self.fix_reward(0.98);
            }
        }
    }
    fn minimize_with_biclauses(&mut self, cdb: &ClauseDB, vec: &mut Vec<Lit>) {
        if vec.len() <= 1 {
            return;
        }
        let VarDB { lbd_temp, var, .. } = self;
        let key = lbd_temp[0] + 1;
        // let mut lbd = 0;
        for l in &vec[1..] {
            // if lbd_temp[l.vi() as usize] != key [
            //     lbd += 1;
            //     if 6 < lbd {
            //         return;
            //     }
            // }
            lbd_temp[l.vi() as usize] = key;
        }
        let l0 = vec[0];
        let mut nsat = 0;
        for w in &cdb.watcher[!l0] {
            let c = &cdb[w.c];
            if c.len() != 2 {
                continue;
            }
            debug_assert!(c[0] == l0 || c[1] == l0);
            let other = c[(c[0] == l0) as usize];
            let vi = other.vi();
            if lbd_temp[vi] == key && var[vi].assigned(other) == Some(true) {
                nsat += 1;
                lbd_temp[vi] -= 1;
            }
        }
        if 0 < nsat {
            lbd_temp[l0.vi()] = key;
            vec.retain(|l| lbd_temp[l.vi()] == key);
        }
        lbd_temp[0] = key;
    }
}

impl LBDIF for VarDB {
    fn compute_lbd(&mut self, vec: &[Lit]) -> usize {
        let VarDB { lbd_temp, var, .. } = self;
        unsafe {
            let key: usize = lbd_temp.get_unchecked(0) + 1;
            *lbd_temp.get_unchecked_mut(0) = key;
            let mut cnt = 0;
            for l in vec {
                let lv = var[l.vi()].level;
                let p = lbd_temp.get_unchecked_mut(lv);
                if *p != key {
                    *p = key;
                    cnt += 1;
                }
            }
            cnt
        }
    }
    fn reset_lbd(&mut self, cdb: &mut ClauseDB) {
        let VarDB { lbd_temp, .. } = self;
        unsafe {
            let mut key = *lbd_temp.get_unchecked(0);
            for c in &mut cdb[1..] {
                if c.is(Flag::DEAD) || c.is(Flag::LEARNT) {
                    continue;
                }
                key += 1;
                let mut cnt = 0;
                for l in &c.lits {
                    let lv = self.var[l.vi()].level;
                    if lv != 0 {
                        let p = lbd_temp.get_unchecked_mut(lv);
                        if *p != key {
                            *p = key;
                            cnt += 1;
                        }
                    }
                }
                c.rank = cnt;
            }
            *lbd_temp.get_unchecked_mut(0) = key;
        }
    }
}

impl VarDB {
    // This function is for Reason-Side Rewarding which must traverse the assign stack
    // beyond first UIDs and bump all vars on the traversed tree.
    // If you'd like to use this, you should stop bumping activities in `analyze`.
    #[allow(dead_code)]
    fn bump_vars(&mut self, asgs: &AssignStack, cdb: &ClauseDB, confl: ClauseId) {
        debug_assert_ne!(confl, ClauseId::default());
        let mut cid = confl;
        let mut p = NULL_LIT;
        let mut ti = asgs.len(); // trail index
        debug_assert!(self.iter().skip(1).all(|v| !v.is(Flag::VR_SEEN)));
        loop {
            for q in &cdb[cid].lits[(p != NULL_LIT) as usize..] {
                let vi = q.vi();
                if !self.var[vi].is(Flag::VR_SEEN) {
                    self.var[vi].turn_on(Flag::VR_SEEN);
                    self.reward_at_analysis(vi);
                }
            }
            loop {
                if 0 == ti {
                    self.var[asgs[ti].vi()].turn_off(Flag::VR_SEEN);
                    debug_assert!(self.iter().skip(1).all(|v| !v.is(Flag::VR_SEEN)));
                    return;
                }
                ti -= 1;
                p = asgs[ti];
                let next_vi = p.vi();
                if self.var[next_vi].is(Flag::VR_SEEN) {
                    self.var[next_vi].turn_off(Flag::VR_SEEN);
                    cid = self.var[next_vi].reason;
                    if cid != ClauseId::default() {
                        break;
                    }
                }
            }
        }
    }
    #[allow(dead_code)]
    fn dump_dependency(&mut self, asgs: &AssignStack, cdb: &ClauseDB, confl: ClauseId) {
        debug_assert_ne!(confl, ClauseId::default());
        let mut cid = confl;
        let mut p = NULL_LIT;
        let mut ti = asgs.len(); // trail index
        debug_assert!(self.iter().skip(1).all(|v| !v.is(Flag::VR_SEEN)));
        println!();
        loop {
            for q in &cdb[cid].lits[(p != NULL_LIT) as usize..] {
                let vi = q.vi();
                if !self.var[vi].is(Flag::VR_SEEN) {
                    self.var[vi].turn_on(Flag::VR_SEEN);
                    println!(" - {}: {}: set", cid, self.var[vi]);
                }
            }
            loop {
                if 0 == ti {
                    self.var[asgs[ti].vi()].turn_off(Flag::VR_SEEN);
                    debug_assert!(self.iter().skip(1).all(|v| !v.is(Flag::VR_SEEN)));
                    println!();
                    return;
                }
                ti -= 1;
                p = asgs[ti];
                let next_vi = p.vi();
                if self.var[next_vi].is(Flag::VR_SEEN) {
                    self.var[next_vi].turn_off(Flag::VR_SEEN);
                    cid = self.var[next_vi].reason;
                    if cid != ClauseId::default() {
                        break;
                    }
                }
            }
        }
    }
}

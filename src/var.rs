/// Crate `var` provides `var` object and its manager `VarDB`.
use {
    crate::{
        clause::{Clause, ClauseDB, ClauseIF, ClauseId},
        config::Config,
        propagator::{AssignStack, PropagatorIF},
        state::{ProgressComponent, SearchStrategy, Stat, State},
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
    /// minimize a clause.
    fn minimize_with_biclauses(&mut self, cdb: &ClauseDB, vec: &mut Vec<Lit>);
}

/// API for var rewarding.
pub trait VarRewardIF {
    /// return var's activity.
    fn activity(&mut self, vi: VarId) -> f64;
    /// initialize rewards based on an order of vars.
    fn initialize_reward(&mut self, iterator: Iter<'_, usize>);
    /// clear var's activity
    fn clear_reward(&mut self, vi: VarId);
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
    pub level: DecisionLevel,
    /// the number of participation in conflict analysis
    participated: u32,
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
            self.reason,
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

/// A container of variables.
#[derive(Debug)]
pub struct VarDB {
    /// var activity decay
    activity_decay: f64,
    /// maximum var activity decay
    activity_decay_max: f64,
    /// an index for counting elapsed time
    ordinal: usize,
    /// vars
    var: Vec<Var>,
    /// estimated number of hot variable
    core_size: Ema,
    /// a working buffer for LBD calculation
    lbd_temp: Vec<usize>,
    #[cfg(feature = "EVSIDS")]
    reward_step: f64,
}

const CORE_HISOTRY_LEN: usize = 10;

impl Default for VarDB {
    #[cfg(not(feature = "EVSIDS"))]
    fn default() -> VarDB {
        const VRD_MAX: f64 = 0.96;
        const VRD_START: f64 = 0.8;
        VarDB {
            activity_decay: VRD_START,
            activity_decay_max: VRD_MAX,
            ordinal: 0,
            var: Vec::new(),
            core_size: Ema::new(CORE_HISOTRY_LEN),
            lbd_temp: Vec::new(),
        }
    }
    #[cfg(feature = "EVSIDS")]
    fn default() -> VarDB {
        const VRD_MAX: f64 = 0.96;
        const VRD_START: f64 = 0.8;
        VarDB {
            activity_decay: VRD_START,
            activity_decay_max: VRD_MAX,
            ordinal: 0,
            var: Vec::new(),
            core_size: Ema::new(CORE_HISOTRY_LEN),
            lbd_temp: Vec::new(),
            reward_step: 0.000_000_1,
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
    fn initialize_reward(&mut self, _iterator: Iter<'_, usize>) {}
    fn clear_reward(&mut self, vi: VarId) {
        self[vi].reward = 0.0;
    }

    //
    // EVSIDS
    //
    #[cfg(feature = "EVSIDS")]
    fn reward_at_analysis(&mut self, vi: VarId) {
        let s = self.reward_step;
        let v = &mut self[vi];
        v.reward += s;
        const SCALE: f64 = 1e-30;
        const SCALE_MAX: f64 = 1e240;
        if SCALE_MAX  < v.reward {
            for v in &mut self.var[1..] {
                v.reward *= SCALE;
            }
            self.reward_step *= SCALE;
        }
    }
    #[cfg(feature = "EVSIDS")]
    fn reward_at_assign(&mut self, _: VarId) {}
    #[cfg(feature = "EVSIDS")]
    fn reward_at_unassign(&mut self, _: VarId) {}
    #[cfg(feature = "EVSIDS")]
    fn reward_update(&mut self) {
        const INC_SCALE: f64 = 1.001;
        self.reward_step *= INC_SCALE;
    }

    //
    // Learning Rate
    //
    #[cfg(not(feature = "EVSIDS"))]
    fn reward_at_analysis(&mut self, vi: VarId) {
        let v = &mut self[vi];
        v.participated += 1;
    }
    #[cfg(not(feature = "EVSIDS"))]
    fn reward_at_assign(&mut self, vi: VarId) {
        let t = self.ordinal;
        let v = &mut self[vi];
        v.timestamp = t;
    }
    #[cfg(not(feature = "EVSIDS"))]
    fn reward_at_unassign(&mut self, vi: VarId) {
        let v = &mut self.var[vi];
        let duration = (self.ordinal + 1 - v.timestamp) as f64;
        let decay = self.activity_decay;
        let rate = v.participated as f64 / duration;
        v.reward *= decay;
        v.reward += (1.0 - decay) * rate;
        v.participated = 0;
    }
    #[cfg(not(feature = "EVSIDS"))]
    fn reward_update(&mut self) {
        const VRD_STEP: f64 = 0.000_01;
        self.ordinal += 1;
        self.activity_decay = self.activity_decay_max.min(self.activity_decay + VRD_STEP);
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
    fn adapt_to(&mut self, state: &State) {
        if 0 == state[Stat::Conflict] {
            let nv = self.var.len();
            self.core_size.update(((CORE_HISOTRY_LEN * nv) as f64).ln());
            return;
        }
        const VRD_DEC_STRICT: f64 = 0.001;
        const VRD_DEC_STD: f64 = 0.003;
        const VRD_DEC_HIGH: f64 = 0.008;
        const VRD_FILTER: f64 = 0.5;
        const VRD_INTERVAL: usize = 20_000;
        const VRD_MAX_START: f64 = 0.2;
        const VRD_OFFSET: f64 = 10.0;
        let msr: (f64, f64) = self.var[1..]
            .iter()
            .map(|v| v.reward)
            .fold((VRD_MAX_START, 0.0), |(m, s), x| (m.max(x), s + x));
        let ar = msr.1 / self.var.len() as f64;
        let thr = msr.0 * VRD_FILTER + ar * (1.0 - VRD_FILTER);
        let core = self.var[1..].iter().filter(|v| thr <= v.reward).count();
        self.core_size.update(core as f64);
        if state[Stat::Conflict] % VRD_INTERVAL == 0 {
            let k = match state.strategy.0 {
                SearchStrategy::LowDecisions => VRD_DEC_HIGH,
                SearchStrategy::HighSuccesive => VRD_DEC_STRICT,
                _ => VRD_DEC_STD,
            };
            let c = (self.core_size.get() - VRD_OFFSET).max(1.0);
            let delta = 0.1 * k * (c.sqrt() * c.ln());
            self.activity_decay_max = 1.0 - delta;
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
    fn minimize_with_biclauses(&mut self, cdb: &ClauseDB, vec: &mut Vec<Lit>) {
        if vec.len() <= 1 {
            return;
        }
        let VarDB { lbd_temp, var, .. } = self;
        let key = lbd_temp[0] + 1;
        for l in &vec[1..] {
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
                let p = lbd_temp.get_unchecked_mut(lv as usize);
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
                        let p = lbd_temp.get_unchecked_mut(lv as usize);
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

impl ProgressComponent for VarDB {
    type Output = (f64, f64);
    fn progress_component(&self) -> Self::Output {
        (self.core_size.get(), self.activity_decay)
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

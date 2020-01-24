use {
    crate::{
        clause::{Clause, ClauseDB, ClauseIF, ClauseId, ClauseIdIF},
        config::Config,
        propagator::{AssignStack, PropagatorIF},
        types::*,
    },
    std::{
        fmt, iter,
        ops::{Index, IndexMut, Range, RangeFrom},
    },
};

/// API for 'watcher list' like `attach`, `detach`, `detach_with` and so on.
pub trait LBDIF {
    /// return a LBD value for the set of literals.
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
    /// return the 'value' of a given literal.
    fn assigned(&self, l: Lit) -> Option<bool>;
    /// return `true` is the clause is the reason of the assignment.
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool;
    /// return `true` if the set of literals is satisfiable under the current assignment.
    fn satisfies(&self, c: &[Lit]) -> bool;
    /// update internal counter..
    fn update(&mut self);
    /// initialize rewards based on an order of vars.
    fn initialize_reward(
        &mut self,
        iterator: iter::Skip<iter::Enumerate<std::slice::Iter<'_, usize>>>,
    );
    // minimize a clause.
    fn minimize_with_bi_clauses(&mut self, cdb: &ClauseDB, vec: &mut Vec<Lit>);
    // bump vars' activities.
    fn bump_vars(&mut self, asgs: &AssignStack, cdb: &ClauseDB, confl: ClauseId);
}

const VAR_ACTIVITY_DECAY: f64 = 0.94;

/// Structure for variables.
#[derive(Debug)]
pub struct Var {
    /// reverse conversion to index. Note `VarId` must be `usize`.
    pub index: VarId,
    /// the current value.
    pub assign: Option<bool>,
    /// the previous assigned value
    pub phase: bool,
    /// the propagating clause
    pub reason: ClauseId,
    /// decision level at which this variables is assigned.
    pub level: usize,
    /// a dynamic evaluation criterion like VSIDS or ACID.
    reward: f64,
    /// the number of conflicts at which this var was rewarded lastly.
    timestamp: usize,
    /// list of clauses which contain this variable positively.
    pub pos_occurs: Vec<ClauseId>,
    /// list of clauses which contain this variable negatively.
    pub neg_occurs: Vec<ClauseId>,
    /// the `Flag`s
    flags: Flag,
}

impl Default for Var {
    fn default() -> Var {
        Var {
            index: 0,
            assign: None,
            phase: false,
            reason: ClauseId::default(),
            level: 0,
            reward: 0.0,
            timestamp: 0,
            pos_occurs: Vec::new(),
            neg_occurs: Vec::new(),
            flags: Flag::empty(),
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
    fn is(&self, flag: Flag) -> bool {
        self.flags.contains(flag)
    }
    fn turn_off(&mut self, flag: Flag) {
        self.flags.remove(flag);
    }
    fn turn_on(&mut self, flag: Flag) {
        self.flags.insert(flag);
    }
}

/// Structure for variables.
#[derive(Debug)]
pub struct VarDB {
    activity_decay: f64,
    ordinal: usize,
    /// vars
    var: Vec<Var>,
    /// a working buffer for LBD calculation
    lbd_temp: Vec<usize>,
}

impl Default for VarDB {
    fn default() -> VarDB {
        VarDB {
            activity_decay: VAR_ACTIVITY_DECAY,
            ordinal: 0,
            var: Vec::new(),
            lbd_temp: Vec::new(),
        }
    }
}

impl Index<usize> for VarDB {
    type Output = Var;
    #[inline]
    fn index(&self, i: usize) -> &Var {
        unsafe { self.var.get_unchecked(i) }
    }
}

impl IndexMut<usize> for VarDB {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Var {
        unsafe { self.var.get_unchecked_mut(i) }
    }
}

impl Index<Range<usize>> for VarDB {
    type Output = [Var];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Var] {
        &self.var[r]
    }
}

impl Index<RangeFrom<usize>> for VarDB {
    type Output = [Var];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Var] {
        unsafe { self.var.get_unchecked(r) }
    }
}

impl IndexMut<Range<usize>> for VarDB {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Var] {
        unsafe { self.var.get_unchecked_mut(r) }
    }
}

impl IndexMut<RangeFrom<usize>> for VarDB {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Var] {
        &mut self.var[r]
    }
}

impl ActivityIF for VarDB {
    type Ix = VarId;
    type Inc = usize;
    fn activity(&mut self, vi: Self::Ix) -> f64 {
        let now = self.ordinal;
        let v = &mut self.var[vi];
        let diff = now - v.timestamp;
        if 0 < diff {
            v.timestamp = now;
            v.reward *= self.activity_decay.powi(diff as i32);
        }
        v.reward
    }
    fn bump_activity(&mut self, vi: Self::Ix, dl: Self::Inc) {
        let v = &mut self.var[vi];
        let now = self.ordinal;
        let t = (now - v.timestamp) as i32;
        // v.reward = (now as f64 + self.activity) / 2.0; // ASCID
        v.reward =
            0.2 + 1.0 / (dl + 1) as f64 + v.reward * self.activity_decay.powi(t);
        v.timestamp = now;
    }
    fn scale_activity(&mut self) {}
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
    fn update(&mut self) {
        self.ordinal += 1;
    }
    fn initialize_reward(
        &mut self,
        iterator: iter::Skip<iter::Enumerate<std::slice::Iter<'_, usize>>>,
    ) {
        let _nv = self.len();
        for (_, vi) in iterator {
            self.var[*vi].reward = 0.0; // (nv - i) as f64; // big bang initialization
        }
    }
    fn minimize_with_bi_clauses(&mut self, cdb: &ClauseDB, vec: &mut Vec<Lit>) {
        let nlevels = self.compute_lbd(vec);
        let VarDB { lbd_temp, var, .. } = self;
        if 6 < nlevels {
            return;
        }
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
    // This function is for Reason-Side Rewarding which must traverse the assign stack
    // beyond first UIDs and bump all vars on the traversed tree.
    // If you'd like to use this, you should stop bumping activities in `analyze`.
    fn bump_vars(&mut self, asgs: &AssignStack, cdb: &ClauseDB, confl: ClauseId) {
        debug_assert_ne!(confl, ClauseId::default());
        let mut cid = confl;
        let mut p = NULL_LIT;
        let mut ti = asgs.len(); // trail index
        debug_assert!(self.var[1..].iter().all(|v| !v.is(Flag::VR_SEEN)));
        loop {
            for q in &cdb[cid].lits[(p != NULL_LIT) as usize..] {
                let vi = q.vi();
                if !self.var[vi].is(Flag::VR_SEEN) {
                    self.var[vi].turn_on(Flag::VR_SEEN);
                    self.bump_activity(vi, 0);
                }
            }
            loop {
                if 0 == ti {
                    self.var[asgs.trail[ti].vi()].turn_off(Flag::VR_SEEN);
                    debug_assert!(self.var[1..].iter().all(|v| !v.is(Flag::VR_SEEN)));
                    return;
                }
                ti -= 1;
                p = asgs.trail[ti];
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
    pub fn dump_dependency(&mut self, asgs: &AssignStack, cdb: &ClauseDB, confl: ClauseId) {
        debug_assert_ne!(confl, ClauseId::default());
        let mut cid = confl;
        let mut p = NULL_LIT;
        let mut ti = asgs.len(); // trail index
        debug_assert!(self.var[1..].iter().all(|v| !v.is(Flag::VR_SEEN)));
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
                    self.var[asgs.trail[ti].vi()].turn_off(Flag::VR_SEEN);
                    debug_assert!(self.var[1..].iter().all(|v| !v.is(Flag::VR_SEEN)));
                    println!();
                    return;
                }
                ti -= 1;
                p = asgs.trail[ti];
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

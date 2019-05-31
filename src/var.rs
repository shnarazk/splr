use crate::clause::Clause;
use crate::state::{Stat, State};
use crate::traits::*;
use crate::types::*;
use std::fmt;

const VAR_ACTIVITY_DECAY: f64 = 0.96;

/// Structure for variables.
#[derive(Debug)]
pub struct Var {
    /// reverse conversion to index. Note `VarId` must be `usize`.
    pub index: VarId,
    /// the current value.
    pub assign: Lbool,
    /// the previous assigned value
    pub phase: Lbool,
    pub reason: ClauseId,
    /// decision level at which this variables is assigned.
    pub level: usize,
    /// a dynamic evaluation criterion like VSIDS or ACID.
    pub reward: f64,
    /// list of clauses which contain this variable positively.
    pub pos_occurs: Vec<ClauseId>,
    /// list of clauses which contain this variable negatively.
    pub neg_occurs: Vec<ClauseId>,
    flags: Flag,
    /// PLRC
    pub num_used: usize,
    pub num_learned: usize,
    pub last_update: usize,
}

/// is the dummy var index.
#[allow(dead_code)]
const NULL_VAR: VarId = 0;

impl VarIF for Var {
    fn new(i: usize) -> Var {
        Var {
            index: i,
            assign: BOTTOM,
            phase: BOTTOM,
            reason: NULL_CLAUSE,
            level: 0,
            reward: 0.0,
            pos_occurs: Vec::new(),
            neg_occurs: Vec::new(),
            flags: Flag::empty(),
            num_used: 0,
            num_learned: 0,
            last_update: 0,
        }
    }
    fn new_vars(n: usize) -> Vec<Var> {
        let mut vec = Vec::with_capacity(n + 1);
        for i in 0..=n {
            let mut v = Var::new(i);
            v.reward = (n - i) as f64;
            vec.push(v);
        }
        vec
    }
    fn activity(&mut self, nconfl: usize) -> f64 {
        /*
        // EVSIDS modified
        let diff = present - self.last_update;
        if 0 < diff {
            self.last_update = present;
            self.reward *= VAR_ACTIVITY_DECAY.powi(diff as i32);
        }
        */
        // /*
        // CHB modified
        let diff = self.num_used;
        if 0 < diff {
            let diff = nconfl - self.last_update;
            self.reward =
                1.0 / (diff + 1) as f64 + self.reward * VAR_ACTIVITY_DECAY.powi(diff as i32);
            self.num_used = 0;
        }
        // */
        self.reward
    }
    fn bump_activity(&mut self, state: &mut State, _dl: usize) {
        /*
        // EVSIDS modified
        let diff = state.stats[Stat::Conflict] - self.last_update;
        self.reward =
            0.2 + 1.0 / (dl + 1) as f64 + self.reward * VAR_ACTIVITY_DECAY.powi(diff as i32);
        */
        // /*
        // CHB modified
        self.last_update = state.stats[Stat::Conflict];
        // */
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

impl VarDBIF for [Var] {
    fn assigned(&self, l: Lit) -> Lbool {
        unsafe { self.get_unchecked(l.vi()).assign ^ ((l & 1) as u8) }
    }
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool {
        let lits = &c.lits;
        debug_assert!(1 < lits.len());
        let l0 = lits[0];
        self.assigned(l0) == TRUE && self[l0.vi()].reason == cid
    }
    fn satisfies(&self, vec: &[Lit]) -> bool {
        for l in vec {
            if self.assigned(*l) == TRUE {
                return true;
            }
        }
        false
    }
    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize {
        let key = keys[0] + 1;
        let mut cnt = 0;
        for l in vec {
            let lv = self[l.vi()].level;
            if keys[lv] != key {
                keys[lv] = key;
                cnt += 1;
            }
        }
        keys[0] = key;
        cnt
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(
            f,
            "V{}({} at {} by {} {}{})",
            self.index,
            self.assign,
            self.level,
            self.reason.format(),
            st(Flag::TOUCHED, ", touched"),
            st(Flag::ELIMINATED, ", eliminated"),
        )
    }
}

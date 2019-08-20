use crate::clause::Clause;
use crate::traits::*;
use crate::types::*;
use std::fmt;
use std::ops::{Index, IndexMut, Range, RangeFrom};

const VAR_ACTIVITY_DECAY: f64 = 0.92;

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
    /// for EMA-based activity
    pub last_used: usize,
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
            last_used: 0,
        }
    }
    fn new_vars(n: usize) -> Vec<Var> {
        let mut vec = Vec::with_capacity(n + 1);
        for i in 0..=n {
            vec.push(Var::new(i));
        }
        vec
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
    /// vars
    pub vars: Vec<Var>,
    /// the current conflict number
    /// var activity decay
    pub activity_decay: f64,
    pub current_conflict: usize,
    pub lbd_temp: Vec<usize>,
}

impl Default for VarDB {
    fn default() -> VarDB {
        VarDB {
            vars: Vec::new(),
            activity_decay: VAR_ACTIVITY_DECAY,
            current_conflict: 0,
            lbd_temp: Vec::new(),
        }
    }
}

impl Index<usize> for VarDB {
    type Output = Var;
    #[inline]
    fn index(&self, i: usize) -> &Var {
        &self.vars[i]
    }
}

impl IndexMut<usize> for VarDB {
    #[inline]
    fn index_mut(&mut self, i: usize) -> &mut Var {
        &mut self.vars[i]
    }
}

impl Index<Range<usize>> for VarDB {
    type Output = [Var];
    #[inline]
    fn index(&self, r: Range<usize>) -> &[Var] {
        &self.vars[r]
    }
}

impl Index<RangeFrom<usize>> for VarDB {
    type Output = [Var];
    #[inline]
    fn index(&self, r: RangeFrom<usize>) -> &[Var] {
        &self.vars[r]
    }
}

impl IndexMut<Range<usize>> for VarDB {
    #[inline]
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Var] {
        &mut self.vars[r]
    }
}

impl IndexMut<RangeFrom<usize>> for VarDB {
    #[inline]
    fn index_mut(&mut self, r: RangeFrom<usize>) -> &mut [Var] {
        &mut self.vars[r]
    }
}

impl VarDBIF for VarDB {
    fn new(n: usize, activity_decay: f64) -> Self {
        VarDB {
            vars: Var::new_vars(n),
            activity_decay,
            current_conflict: 0,
            lbd_temp: vec![0; n + 1],
        }
    }
    fn assigned(&self, l: Lit) -> Lbool {
        unsafe { self.vars.get_unchecked(l.vi()).assign ^ ((l & 1) as u8) }
    }
    fn locked(&self, c: &Clause, cid: ClauseId) -> bool {
        let lits = &c.lits;
        debug_assert!(1 < lits.len());
        let l0 = lits[0];
        self.assigned(l0) == TRUE && self.vars[l0.vi()].reason == cid
    }
    fn satisfies(&self, vec: &[Lit]) -> bool {
        for l in vec {
            if self.assigned(*l) == TRUE {
                return true;
            }
        }
        false
    }
    fn compute_lbd(&mut self, vec: &[Lit]) -> usize {
        let key = self.lbd_temp[0] + 1;
        let mut cnt = 0;
        for l in vec {
            let lv = self.vars[l.vi()].level;
            if self.lbd_temp[lv] != key {
                self.lbd_temp[lv] = key;
                cnt += 1;
            }
        }
        self.lbd_temp[0] = key;
        cnt
    }
    fn activity(&mut self, vi: VarId) -> f64 {
        let v = &mut self.vars[vi];
        if self.current_conflict != v.last_used {
            let diff = self.current_conflict - v.last_used;
            let decay = self.activity_decay;
            v.last_used = self.current_conflict;
            // assert!(0.0 <= decay, format!("decay {}", decay));
            v.reward *= decay.powi(diff as i32);
        }
        v.reward
    }
    fn bump_activity(&mut self, vi: VarId) {
        self.activity(vi);
        self.vars[vi].reward += 1.0 - self.activity_decay;
    }
}

impl VarDB {
    #[allow(dead_code)]
    fn force_reset(&mut self, ncnfl: usize) -> bool {
        let mut cnt = 20_000;
        let mut modified: bool = false;
        for v in &mut self.vars[1..] {
            if !v.is(Flag::ELIMINATED) && v.reward == 0.0 && 0 < v.level && 0 < cnt {
                v.reward = 1.0;
                v.last_used = ncnfl;
                modified = true;
                cnt -= 1;
            }
        }
        modified
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(
            f,
            "V{}({} at {} by {} {}{}{})",
            self.index,
            self.assign,
            self.level,
            self.reason.format(),
            st(Flag::TOUCHED, ", touched"),
            st(Flag::ELIMINATED, ", eliminated"),
            st(Flag::FUP, ", fup"),
        )
    }
}

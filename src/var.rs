use crate::clause::Clause;
use crate::config::{Config, ACTIVITY_MAX};
use crate::state::{Stat, State};
use crate::traits::*;
use crate::types::*;
use std::fmt;
use std::ops::{Index, IndexMut, Range, RangeFrom};

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
    pub activity: f64,
    /// list of clauses which contain this variable positively.
    pub pos_occurs: Vec<ClauseId>,
    /// list of clauses which contain this variable negatively.
    pub neg_occurs: Vec<ClauseId>,
    flags: Flag,
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
            activity: 0.0,
            pos_occurs: Vec::new(),
            neg_occurs: Vec::new(),
            flags: Flag::empty(),
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
    var: Vec<Var>,
    /// the current conflict's ordinal number
    current_conflict: usize,
    /// the current restart's ordinal number
    current_restart: usize,
    pub lbd_temp: Vec<usize>,
    pub activity_inc: f64,
    pub activity_decay: f64,
    pub activity_decay_max: f64,
}

impl Default for VarDB {
    fn default() -> VarDB {
        VarDB {
            var: Vec::new(),
            current_conflict: 0,
            current_restart: 0,
            lbd_temp: Vec::new(),
            activity_inc: 1.0,
            activity_decay: 0.9,
            activity_decay_max: 0.95,
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
    fn bump_activity(&mut self, vi: Self::Ix) {
        let v = &mut self.var[vi];
        let a = v.activity + self.activity_inc;
        v.activity = a;
        if ACTIVITY_MAX < a {
            let scale = 1.0 / self.activity_inc;
            for v in &mut self[1..] {
                v.activity *= scale;
            }
            self.activity_inc *= scale;
        }
    }
    fn scale_activity(&mut self) {
        self.activity_inc /= self.activity_decay;
    }
}

impl Instantiate for VarDB {
    fn instantiate(_: &Config, cnf: &CNFDescription) -> Self {
        let nv = cnf.num_of_variables;
        VarDB {
            var: Var::new_vars(nv),
            current_conflict: 0,
            current_restart: 0,
            lbd_temp: vec![0; nv + 1],
            activity_inc: 1.0,
            activity_decay: 0.9,
            activity_decay_max: 0.95,
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
    fn assigned(&self, l: Lit) -> Lbool {
        unsafe { self.var.get_unchecked(l.vi()).assign ^ ((l & 1) as u8) }
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
    fn update_stat(&mut self, state: &State) {
        self.current_conflict = state.stats[Stat::Conflict] + 1;
        self.current_restart = state.stats[Stat::Restart] + 1;
    }

    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize {
        unsafe {
            let key = keys.get_unchecked(0) + 1;
            let mut cnt = 0;
            for l in vec {
                let lv = self[l.vi()].level;
                let p = keys.get_unchecked_mut(lv);
                if  *p != key {
                    *p = key;
                    cnt += 1;
                }
            }
            *keys.get_unchecked_mut(0) = key;
            cnt
        }
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

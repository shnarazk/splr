use crate::clause::Clause;
use crate::restart::Ema2;
use crate::traits::*;
use crate::types::*;
use std::fmt;
use std::ops::{Index, IndexMut, Range};

const EMA_SLOW: usize = 8192; // 2 ^ 13; 2 ^ 15 = 32768
const EMA_FAST: usize = 64; // 2 ^ 6
const VAR_ACTIVITY_DECAY: f64 = 0.92;
const CLOSE_THRD: f64 = 0.5; // 0.72;

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

#[derive(Debug)]
pub struct VarSet {
    pub flag: Option<Flag>,
    pub num: usize,
    pub diff: f64,
    pub diff_ema: Ema2,
    pub is_closed: bool,
    pub threshold: f64,
}

impl VarSetIF for VarSet {
    fn new(flag: Option<Flag>, threshold: f64) -> Self {
        VarSet {
            flag,
            num: 0,
            diff: 0.0,
            diff_ema: Ema2::new(EMA_SLOW).with_fast(EMA_FAST).initialize1(),
            is_closed: false,
            threshold,
        }
    }
    fn add(&mut self, v: &mut Var) {
        match self.flag {
            Some(flag) => {
                if !v.is(flag) {
                    v.turn_on(flag);
                    self.num += 1;
                    self.diff += 1.0;
                }
            }
            None => {
                self.num += 1;
                self.diff += 1.0;
            }
        }
    }
    fn remove(&self, v: &mut Var) {
        if let Some(flag) = self.flag {
            if v.is(flag) {
                v.turn_off(flag);
            }
        }
    }
    fn reset(&mut self) {
        self.num = 0;
        self.diff = 0.0;
        self.is_closed = false;
        self.diff_ema.reinitialize1();
    }
    fn commit(&mut self) {
        self.diff_ema.update(self.diff as f64);
        self.diff = 0.0;
    }
    fn check<F>(&mut self, f: F) -> bool
    where
        F: Fn(f64, f64, f64) -> bool,
    {
        let long = self.diff_ema.get();
        let rate = self.diff_ema.get_fast();
        let thrd = self.threshold;
        // let v = rate < thrd && long < thrd && rate < long;
        let v = f(long, rate, thrd);
        if !self.is_closed {
            self.diff_ema.update(self.diff as f64);
            self.diff = 0.0;
            if v {
                self.is_closed = true;
                return true;
            }
        }
        false
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

    /// ### About levels
    ///
    /// - Level 0 is a memory cleared at each restart
    /// - Level 1 is a memory held during restarts but clear after mega-restart
    /// - Level 2 is a memory not to reset by restarts
    /// *Note: all levels clear after finding a unit learnt (simplification).*

    /// Level 0 good old no-memory ASsigned Variable
    pub asv: VarSet,
    pub acv: VarSet,
    pub sua: VarSet,
    pub fup: VarSet,
    pub suf: VarSet,
    pub current_conflict: usize,
    pub lbd_temp: Vec<usize>,
}

impl Default for VarDB {
    fn default() -> VarDB {
        VarDB {
            vars: Vec::new(),
            activity_decay: VAR_ACTIVITY_DECAY,

            asv: VarSet::new(None, CLOSE_THRD),
            acv: VarSet::new(Some(Flag::ACV), CLOSE_THRD),
            sua: VarSet::new(Some(Flag::SUA), CLOSE_THRD),
            fup: VarSet::new(Some(Flag::FUP), CLOSE_THRD),
            suf: VarSet::new(Some(Flag::SUF), CLOSE_THRD),
            current_conflict: 0,
            lbd_temp: Vec::new(),
        }
    }
}

impl Index<usize> for VarDB {
    type Output = Var;
    fn index(&self, i: usize) -> &Var {
        &self.vars[i]
    }
}

impl IndexMut<usize> for VarDB {
    fn index_mut(&mut self, i: usize) -> &mut Var {
        &mut self.vars[i]
    }
}

impl Index<Range<usize>> for VarDB {
    type Output = [Var];
    fn index(&self, r: Range<usize>) -> &[Var] {
        &self.vars[r]
    }
}

impl IndexMut<Range<usize>> for VarDB {
    fn index_mut(&mut self, r: Range<usize>) -> &mut [Var] {
        &mut self.vars[r]
    }
}

impl VarDBIF for VarDB {
    fn new(n: usize, activity_decay: f64) -> Self {
        let scale: f64 = (n as f64).log(2f64);
        VarDB {
            vars: Var::new_vars(n),
            activity_decay,

            // asv: VarSet::new(None, 0.5),
            asv: VarSet::new(None, CLOSE_THRD * scale),
            acv: VarSet::new(Some(Flag::ACV), CLOSE_THRD * scale),
            sua: VarSet::new(Some(Flag::SUA), CLOSE_THRD * scale),
            fup: VarSet::new(Some(Flag::FUP), 0.05),
            suf: VarSet::new(Some(Flag::SUF), CLOSE_THRD),
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

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let st = |flag, mes| if self.is(flag) { mes } else { "" };
        write!(
            f,
            "V{}({} at {} by {} {}{}{}{})",
            self.index,
            self.assign,
            self.level,
            self.reason.format(),
            st(Flag::TOUCHED, ", touched"),
            st(Flag::ELIMINATED, ", eliminated"),
            st(Flag::SUF, ", suf"),
            st(Flag::FUP, ", fup"),
        )
    }
}

use crate::clause::Clause;
use crate::restart::Ema2;
use crate::traits::*;
use crate::types::*;
use std::fmt;

const VAR_ACTIVITY_DECAY: f64 = 0.92;
const STAGNATION_THRESHOLD: f64 = 0.72;

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
    pub flag: Flag,
    pub num: usize,
    pub diff: f64,
    pub diff_ema: Ema2,
    pub is_closed: bool,
    pub threshold: f64,
}

impl VarSet {
    pub fn add(&mut self, v: &mut Var) {
        if !v.is(self.flag) {
            v.turn_on(self.flag);
            self.num += 1;
            self.diff += 1.0;
        }
    }
    pub fn reset(&mut self) {
        self.num = 0;
        self.diff = 0.0;
        self.is_closed = false;
        self.diff_ema.reinitialize1();
    }
    fn commit(&mut self) {
        self.diff_ema.update(self.diff as f64);
        self.diff = 0.0;
    }
    fn update(&mut self) -> bool {
        let long = self.diff_ema.get();
        let rate = self.diff_ema.get_fast();
        let thrd = self.threshold;
        let v = rate < thrd && long < thrd && rate < long;
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
    /// - Level 1 is bascially a memory held during restarts
    /// - Level 2 is a memory to clear Level 1 data

    /// Level 0 good old no-memory ASsigned Variable
    pub num_asv: usize,
    pub asv_inc: f64,
    pub asv_is_closed: bool,
    pub asv_threshold: f64,


    /// Level 1: assigned or cancelled variable
    pub num_acv: usize,
    pub acv_inc: f64,
    pub acv_is_closed: bool,
    pub acv_stagnation_threshold: f64,

    /// Level 2: superium of AVS
    pub num_sua: usize,
    pub sua_inc: f64,
    pub sua_is_closed: bool,
    pub sua_stagnation_threshold: f64,

    /// Level 1: First Unified implication Point
    pub num_fup: usize,
    pub fup_inc: f64,
    pub fup_is_closed: bool,
    pub fup_stagnation_threshold: f64,

    /// Level 2: superium of FUP
    pub num_suf: usize,
    pub suf_inc: f64,
    pub suf_is_closed: bool,
    pub suf_stagnation_threshold: f64,

    pub current_conflict: usize,
    pub lbd_temp: Vec<usize>,
}

impl Default for VarDB {
    fn default() -> VarDB {
        VarDB {
            vars: Vec::new(),
            activity_decay: VAR_ACTIVITY_DECAY,

            num_asv: 0,
            asv_inc: 0.0,
            asv_is_closed: false,
            asv_threshold: STAGNATION_THRESHOLD,

            num_acv: 0,
            acv_inc: 0.0,
            acv_is_closed: false,
            acv_stagnation_threshold: STAGNATION_THRESHOLD,

            num_sua: 0,
            sua_inc: 0.0,
            sua_is_closed: false,
            sua_stagnation_threshold: STAGNATION_THRESHOLD,

            num_fup: 0,
            fup_inc: 0.0,
            fup_is_closed: false,
            fup_stagnation_threshold: STAGNATION_THRESHOLD,

            num_suf: 0,
            suf_inc: 0.0,
            suf_is_closed: false,
            suf_stagnation_threshold: STAGNATION_THRESHOLD,

            current_conflict: 0,
            lbd_temp: Vec::new(),
        }
    }
}

impl VarDBIF for VarDB {
    fn new(n: usize, activity_decay: f64) -> Self {
        let scale: f64 = - (n as f64).log(2f64);
        VarDB {
            vars: Var::new_vars(n),
            activity_decay,

            num_asv: 0,
            asv_inc: 0.0,
            asv_is_closed: false,
            asv_threshold: 0.5,

            num_acv: 0,
            acv_inc: 0.0,
            acv_is_closed: false,
            acv_stagnation_threshold: STAGNATION_THRESHOLD * scale,

            num_sua: 0,
            sua_inc: 0.0,
            sua_is_closed: false,
            sua_stagnation_threshold: STAGNATION_THRESHOLD * scale,

            num_fup: 0,
            fup_inc: 0.0,
            fup_is_closed: false,
            fup_stagnation_threshold: STAGNATION_THRESHOLD,

            num_suf: 0,
            suf_inc: 0.0,
            suf_is_closed: false,
            suf_stagnation_threshold: STAGNATION_THRESHOLD / 10f64,

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
    fn set_acv(&mut self, vi: VarId) -> usize {
        let v = &mut self.vars[vi];
        let ret = !v.is(Flag::ACV) as usize;
        if !v.is(Flag::SUA) {
            v.turn_on(Flag::SUA);
            self.num_sua += 1;
            self.sua_inc += 1.0;
        }
        if !v.is(Flag::ACV) {
            v.turn_on(Flag::ACV);
            self.num_acv += 1;
        }
        ret
    }
    fn set_fup(&mut self, vi: VarId) -> usize {
        let v = &mut self.vars[vi];
        let ret = !v.is(Flag::FUP) as usize;
        if !v.is(Flag::SUF) {
            v.turn_on(Flag::SUF);
            self.num_suf += 1;
            self.suf_inc += 1.0;
        }
        if !v.is(Flag::FUP) {
            v.turn_on(Flag::FUP);
            self.num_fup += 1;
            self.fup_inc += 1.0;
        }
        ret
    }
    fn reset_asv(&mut self) {
        self.num_asv = 0;
        self.asv_inc = 0.0;
        self.asv_is_closed = false;
    }
    fn reset_acv(&mut self) {
        for v in &mut self.vars[1..] {
            v.turn_off(Flag::ACV);
        }
        self.num_acv = 0;
        self.acv_inc = 0.0;
        self.acv_is_closed = false;
    }
    fn reset_sua(&mut self) {
        for v in &mut self.vars[1..] {
            v.turn_off(Flag::SUA);
        }
        self.num_sua = 0;
        self.sua_inc = 0.0;
        self.sua_is_closed = false;
    }
    fn reset_fup(&mut self) {
        for v in &mut self.vars[1..] {
            v.turn_off(Flag::FUP);
        }
        self.num_fup = 0;
        self.fup_inc = 0.0;
        self.fup_is_closed = false;
    }

    fn reset_suf(&mut self) {
        for v in &mut self.vars[1..] {
            v.turn_off(Flag::SUF);
        }
        self.num_suf = 0;
        self.suf_inc = 0.0;
        self.suf_is_closed = false;
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

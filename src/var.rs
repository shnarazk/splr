use crate::clause::Clause;
use crate::eliminator::Eliminator;
use crate::traits::*;
use crate::types::*;
use std::fmt;

const VAR_ACTIVITY_MAX: f64 = 1e240;
const VAR_ACTIVITY_SCALE1: f64 = 1e-80;
const VAR_ACTIVITY_SCALE2: f64 = 1e-10;

/// Struct for a variable.
pub struct Var {
    pub index: usize,
    pub assign: Lbool,
    pub phase: Lbool,
    pub reason: ClauseId,
    pub level: usize,
    pub activity: f64,
    pub sve_activity: usize,
    pub pos_occurs: Vec<ClauseId>,
    pub neg_occurs: Vec<ClauseId>,
    flags: u16,
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
            sve_activity: 0,
            pos_occurs: Vec::new(),
            neg_occurs: Vec::new(),
            flags: 0,
        }
    }
    fn new_vars(n: usize) -> Vec<Var> {
        let mut vec = Vec::with_capacity(n + 1);
        for i in 0..=n {
            let mut v = Var::new(i);
            v.activity = (n - i) as f64;
            vec.push(v);
        }
        vec
    }
}

impl FlagIF for Var {
    #[inline(always)]
    fn is(&self, flag: Flag) -> bool {
        self.flags & (1 << flag as u16) != 0
    }
    #[inline(always)]
    fn flag_off(&mut self, flag: Flag) {
        self.flags &= !(1u16 << (flag as u16));
    }
    #[inline(always)]
    fn flag_on(&mut self, flag: Flag) {
        self.flags |= 1u16 << (flag as u16);
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
        self.assigned(l0) == LTRUE && self[l0.vi()].reason == cid
    }
    fn satisfies(&self, vec: &[Lit]) -> bool {
        for l in vec {
            if self.assigned(*l) == LTRUE {
                return true;
            }
        }
        false
    }
    #[inline(always)]
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
    fn attach(&mut self, elim: &mut Eliminator, cid: ClauseId, c: &mut Clause, enqueue: bool) {
        if !elim.in_use {
            return;
        }
        for l in &c.lits {
            let v = &mut self[l.vi()];
            v.flag_on(Flag::TouchedVar);
            if !v.is(Flag::EliminatedVar) {
                if l.positive() {
                    v.pos_occurs.push(cid);
                } else {
                    v.neg_occurs.push(cid);
                }
                elim.enqueue_var(v);
            }
        }
        if enqueue {
            elim.enqueue_clause(cid, c);
        }
    }
    fn detach(&mut self, elim: &mut Eliminator, cid: ClauseId, c: &Clause) {
        debug_assert!(c.is(Flag::DeadClause));
        if elim.in_use {
            for l in &c.lits {
                let v = &mut self[l.vi()];
                if !v.is(Flag::EliminatedVar) {
                    if l.positive() {
                        v.pos_occurs.retain(|&cj| cid != cj);
                    } else {
                        v.neg_occurs.retain(|&cj| cid != cj);
                    }
                    elim.enqueue_var(v);
                }
            }
        }
    }
    fn bump_activity(&mut self, inc: &mut f64, vi: VarId) {
        let v = &mut self[vi];
        let a = v.activity + *inc;
        v.activity = a;
        if VAR_ACTIVITY_MAX < a {
            for v in &mut self[1..] {
                v.activity *= VAR_ACTIVITY_SCALE1;
            }
            *inc *= VAR_ACTIVITY_SCALE2;
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
            st(Flag::TouchedVar, ", touched"),
            st(Flag::EliminatedVar, ", eliminated"),
        )
    }
}

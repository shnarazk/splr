use {
    crate::{
        clause::{Clause, ClauseId},
        config::Config,
        state::{Stat, State},
        traits::*,
        types::*,
    },
    std::{
        fmt, iter,
        ops::{Index, IndexMut, Range, RangeFrom},
    },
};

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
    // /// polarity of assigned value
    // pub polarity: Ema,
    /// frequency of conflict: the reverse of the average conflict interval
    pub foc: Ema,
    /// the propagating clause
    pub reason: ClauseId,
    /// decision level at which this variables is assigned.
    pub level: usize,
    /// a dynamic evaluation criterion like VSIDS or ACID.
    reward: f64,
    /// the number of conflicts at which this var make a conflict.
    last_conflict: usize,
    /// the number of conflicts at which this var was rewarded lastly.
    last_update: usize,
    /// list of clauses which contain this variable positively.
    pub pos_occurs: Vec<ClauseId>,
    /// list of clauses which contain this variable negatively.
    pub neg_occurs: Vec<ClauseId>,
    /// the `Flag`s
    flags: Flag,
}

/// is the dummy var index.
#[allow(dead_code)]
const NULL_VAR: VarId = 0;

impl VarIF for Var {
    fn new(i: usize) -> Var {
        Var {
            index: i,
            assign: None,
            phase: false,
            // polarity: Ema::new(16),
            foc: Ema::new(20),
            reason: ClauseId::default(),
            level: 0,
            reward: 0.0,
            last_conflict: 0,
            last_update: 0,
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
    fn record_conflict(&mut self, now: usize) -> f64 {
        assert_ne!(self.last_conflict, now);
        self.foc
            .update((1.0 / (now - self.last_conflict + 1) as f64).log(2.0));
        self.last_conflict = now;
        self.foc.get()
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
    pub activity_decay: f64,
    pub reward_by_dl: f64,
    // pub reward_by_dl_ema: Ema,
    /// vars
    var: Vec<Var>,
    /// the current conflict's ordinal number
    current_conflict: usize,
    /// the current restart's ordinal number
    current_restart: usize,
    /// a working buffer for LBD calculation
    pub lbd_temp: Vec<usize>,
}

impl Default for VarDB {
    fn default() -> VarDB {
        // let mut reward_by_dl_ema = Ema::new(20);
        // reward_by_dl_ema.update(0.01);
        VarDB {
            activity_decay: VAR_ACTIVITY_DECAY,
            reward_by_dl: 1.0,
            // reward_by_dl_ema,
            var: Vec::new(),
            current_conflict: 0,
            current_restart: 0,
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
        let now = self.current_conflict;
        let v = &mut self.var[vi];
        let diff = now - v.last_update;
        if 0 < diff {
            v.last_update = now;
            v.reward *= self.activity_decay.powi(diff as i32);
        }
        v.reward
    }
    fn bump_activity(&mut self, vi: Self::Ix, dl: Self::Inc) {
        let v = &mut self.var[vi];
        let now = self.current_conflict;
        let t = (now - v.last_update) as i32;
        // v.reward = (now as f64 + self.activity) / 2.0; // ASCID
        v.reward =
            0.2 + self.reward_by_dl / (dl + 1) as f64 + v.reward * self.activity_decay.powi(t);
        v.last_update = now;
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
        // unsafe { self.var.get_unchecked(l.vi()).assign ^ ((l & 1) as u8) }
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
    fn update_stat(&mut self, state: &State) {
        self.current_conflict = state[Stat::Conflict] + 1;
        self.current_restart = state[Stat::Restart] + 1;
    }

    fn compute_lbd(&self, vec: &[Lit], keys: &mut [usize]) -> usize {
        unsafe {
            let key = keys.get_unchecked(0) + 1;
            let mut cnt = 0;
            for l in vec {
                let lv = self[l.vi()].level;
                let p = keys.get_unchecked_mut(lv);
                if *p != key {
                    *p = key;
                    cnt += 1;
                }
            }
            *keys.get_unchecked_mut(0) = key;
            cnt
        }
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

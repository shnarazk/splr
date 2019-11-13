use {
    crate::{
        clause::{ Clause, ClauseDB },
        config::Config,
        propagator::AssignStack,
        state::{ Stat, State },
        traits::*,
        types::*,
    },
    std::{ fmt,
           ops::{ Index, IndexMut, Range, RangeFrom },
    }
};

const ACTIVITY_DECAY: f64 = 0.90;

/// Structure for variables.
#[derive(Clone, Debug)]
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
    pub reward: f64,
    /// the number of conflicts at which this var was rewarded lastly
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
            reason: NULL_CLAUSE,
            level: 0,
            reward: 0.0,
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
#[derive(Clone, Debug)]
pub struct VarDB {
    /// vars
    var: Vec<Var>,
    /// the current conflict's ordinal number
    current_conflict: usize,
    /// the current restart's ordinal number
    current_restart: usize,
    /// a working buffer for LBD calculation
    pub lbd_temp: Vec<usize>,
    pub num_flip: Ema,
}

impl Default for VarDB {
    fn default() -> VarDB {
        VarDB {
            var: Vec::new(),
            current_conflict: 0,
            current_restart: 0,
            lbd_temp: Vec::new(),
            num_flip: Ema::new(32),
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
    fn bump_activity(&mut self, vi: Self::Ix, dl: usize) {
        debug_assert!(0 < dl);
        self.activity(vi);
        let v = &mut self.var[vi];
        v.reward += 0.2 + 1.0 / (dl + 1) as f64;
    }
    fn activity(&mut self, vi: Self::Ix) -> f64 {
        let now = self.current_conflict;
        let v = &mut self.var[vi];
        let t = (now - v.last_update) as i32;
        if 0 < t {
            v.last_update = now;
            v.reward *= ACTIVITY_DECAY.powi(t);

        }
        v.reward
    }
    fn scale_activity(&mut self) {}
}

impl Instantiate for VarDB {
    fn instantiate(_: &Config, cnf: &CNFDescription) -> Self {
        let nv = cnf.num_of_variables;
        VarDB {
            var: Var::new_vars(nv),
            current_conflict: 0,
            current_restart: 0,
            lbd_temp: vec![0; nv + 1],
            num_flip: Ema::new(32),
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
            Some(x) if !l.as_bool() => Some(!x),
            x => x,
        }
    }
    fn minimize_with_bi_clauses(&mut self, cdb: &ClauseDB, vec: &mut Vec<Lit>) {
        let nlevels = self.compute_lbd(vec);
        if 6 < nlevels {
            return;
        }
        let VarDB { ref mut lbd_temp, ref mut var, .. } = self;
        let assigned = |l: Lit| -> Option<bool> {
            match unsafe { var.get_unchecked(l.vi()).assign } {
                Some(x) if !l.as_bool() => Some(!x),
                x => x,
            }
        };
        let key = lbd_temp[0] + 1;
        for l in &vec[1..] {
            lbd_temp[l.vi() as usize] = key;
        }
        let l0 = vec[0];
        let mut nsat = 0;

        for w in &cdb.watcher[l0.negate() as usize] {
            let c = &cdb[w.c];
            if c.lits.len() != 2 {
                continue;
            }
            debug_assert!(c.lits[0] == l0 || c.lits[1] == l0);
            let other = c.lits[(c.lits[0] == l0) as usize];
            let vi = other.vi();
            if lbd_temp[vi] == key && assigned(other) == Some(true) {
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
        self.current_conflict = state.stats[Stat::Conflict] + 1;
        self.current_restart = state.stats[Stat::Restart] + 1;
    }

    fn compute_lbd(&mut self, vec: &[Lit]) -> usize {
        unsafe {
            let key = self.lbd_temp.get_unchecked(0) + 1;
            let mut cnt = 0;
            for l in vec {
                let lv = self[l.vi()].level;
                let p = self.lbd_temp.get_unchecked_mut(lv);
                if *p != key {
                    *p = key;
                    cnt += 1;
                }
            }
            *self.lbd_temp.get_unchecked_mut(0) = key;
            cnt
        }
    }
    /// 20191101-disruption-threshold
    fn restart_conditional(&mut self, asgs: &AssignStack, thr: f64) -> bool {
        let mut flips = 0.0;
        let mut act_pre = self.activity(asgs[0].vi());
        for lv in 1..asgs.level() {
            let vi = asgs[asgs.num_at(lv)].vi();
            assert_eq!(self[vi].reason, NULL_CLAUSE);
            let act = self.activity(vi);
            if act_pre < act {
                flips += 1.0 / (lv + 1) as f64;
            }
            act_pre = act;
        }
        self.num_flip.update(flips);
        thr <= flips
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

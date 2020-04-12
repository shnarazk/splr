/// Crate `var` provides `var` object and its manager `VarDB`.
use {
    crate::{
        assign::AssignIF,
        clause::ClauseDBIF,
        state::{SearchStrategy, State},
        types::*,
    },
    std::{
        fmt,
        ops::{IndexMut, Range, RangeFrom},
        slice::{Iter, IterMut},
    },
};

/// API for var DB like `assigned`, `locked`, and so on.
pub trait VarDBIF: VarPhaseIF
{
    /// return the number of vars.
    fn len(&self) -> usize;
    /// return true if it's empty.
    fn is_empty(&self) -> bool;
    /// return an iterator over vars.
    fn iter(&self) -> Iter<'_, Var>;
    /// return an iterator over vars.
    fn iter_mut(&mut self) -> IterMut<'_, Var>;
}

const CORE_HISOTRY_LEN: usize = 10;

impl Default for VarDB {
    #[cfg(not(feature = "EVSIDS"))]
    fn default() -> VarDB {
        const VRD_MAX: f64 = 0.96;
        const VRD_START: f64 = 0.9;
        VarDB {
            activity_decay: VRD_START,
            activity_decay_max: VRD_MAX,
            ordinal: 0,
//            var: Vec::new(),
            core_size: Ema::new(CORE_HISOTRY_LEN),
            num_var: 0,
        }
    }
    #[cfg(feature = "EVSIDS")]
    fn default() -> VarDB {
        const VRD_MAX: f64 = 0.99;
        const VRD_START: f64 = 0.99;
        VarDB {
            activity_decay: VRD_START,
            activity_decay_max: VRD_MAX,
            ordinal: 0,
//            var: Vec::new(),
            core_size: Ema::new(CORE_HISOTRY_LEN),
            reward_step: 0.000_000_1,
            num_var: 0,
        }
    }
}

/*
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
*/

impl Export<(f64, f64)> for VarDB {
    /// exports:
    ///  1. `core_sise.get()`
    ///  1. `activity_decay`
    ///
    ///```
    /// use crate::{splr::config::Config, splr::types::*};
    /// use crate::splr::var::VarDB;
    /// let vdb = VarDB::instantiate(&Config::default(), &CNFDescription::default());
    ///let (vdb_core_size, vdb_activity_decay) = vdb.exports();
    ///```
    #[inline]
    fn exports(&self) -> (f64, f64) {
        (self.core_size.get(), self.activity_decay)
    }
}

impl Instantiate for VarDB {
    fn instantiate(_: &Config, cnf: &CNFDescription) -> Self {
        let nv = cnf.num_of_variables;
        VarDB {
            // var: Var::new_vars(nv),
            num_var: nv,
            ..VarDB::default()
        }
    }
}

/*
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
    fn iter_mut(&mut self) -> IterMut<'_, Var> {
        self.var.iter_mut()
    }
}
*/

/*
impl VarPhaseIF for VarDB {
    fn save_phase<A>(&mut self, asg: &A, flag: Flag)
    where
        A: AssignIF,
    {
        for l in asg.iter() {
            self.var[l.vi()].set(flag, bool::from(*l));
        }
    }
    fn reset_phase(&mut self, flag: Flag) {
        for v in &mut self.var[1..] {
            v.turn_off(flag);
        }
    }
}
 */

/*
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
        let t = self.ordinal;
        let v = &mut self[vi];
        if v.timestamp == t {
            return;
        }
        v.timestamp = t;
        v.reward += s;
        const SCALE: f64 = 1e-30;
        const SCALE_MAX: f64 = 1e240;
        if SCALE_MAX < v.reward {
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
        self.ordinal += 1;
        const INC_SCALE: f64 = 1.01;
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
 */

/*
impl VarDB {
    // This function is for Reason-Side Rewarding which must traverse the assign stack
    // beyond first UIDs and bump all vars on the traversed tree.
    // If you'd like to use this, you should stop bumping activities in `analyze`.
    #[allow(dead_code)]
    fn bump_vars<A, C>(&mut self, asg: &A, cdb: &C, confl: ClauseId)
    where
        A: AssignIF,
        C: ClauseDBIF,
    {
        debug_assert_ne!(confl, ClauseId::default());
        let mut cid = confl;
        let mut p = NULL_LIT;
        let mut ti = asg.len(); // trail index
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
                    self.var[asg.stack(ti).vi()].turn_off(Flag::VR_SEEN);
                    debug_assert!(self.iter().skip(1).all(|v| !v.is(Flag::VR_SEEN)));
                    return;
                }
                ti -= 1;
                p = asg.stack(ti);
                let next_vi = p.vi();
                if self.var[next_vi].is(Flag::VR_SEEN) {
                    self.var[next_vi].turn_off(Flag::VR_SEEN);
                    if let AssignReason::Implication(c, _) = asg.reason(next_vi) {
                        cid = c;
                        break;
                    }
                }
            }
        }
    }
    #[allow(dead_code)]
    fn dump_dependency<A, C>(&mut self, asg: &A, cdb: &C, confl: ClauseId)
    where
        A: AssignIF,
        C: ClauseDBIF,
    {
        debug_assert_ne!(confl, ClauseId::default());
        let mut cid = confl;
        let mut p = NULL_LIT;
        let mut ti = asg.len(); // trail index
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
                    self.var[asg.stack(ti).vi()].turn_off(Flag::VR_SEEN);
                    debug_assert!(self.iter().skip(1).all(|v| !v.is(Flag::VR_SEEN)));
                    println!();
                    return;
                }
                ti -= 1;
                p = asg.stack(ti);
                let next_vi = p.vi();
                if self.var[next_vi].is(Flag::VR_SEEN) {
                    self.var[next_vi].turn_off(Flag::VR_SEEN);
                    if let AssignReason::Implication(c, _) = asg.reason(next_vi) {
                        cid = c;
                        break;
                    }
                }
            }
        }
    }
}
*/

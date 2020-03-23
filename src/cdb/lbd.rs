use {
    super::{ClauseDB, ClauseId},
    crate::{assign::AssignIF, types::*},
};

/// API to calculate LBD.
pub trait LBDIF {
    /// return the LBD value for a set of literals.
    fn compute_lbd<A>(&mut self, asg: &A, vec: &[Lit]) -> usize
    where
        A: AssignIF;
    /// return the LBD value of clause `cid`.
    fn compute_lbd_of<A>(&mut self, asg: &A, cid: ClauseId) -> usize
    where
        A: AssignIF;
    /// re-calculate the LBD values of all (learnt) clauses.
    fn reset_lbd<A>(&mut self, asg: &A, all: bool)
    where
        A: AssignIF;
}

impl LBDIF for ClauseDB {
    fn compute_lbd<A>(&mut self, asg: &A, vec: &[Lit]) -> usize
    where
        A: AssignIF,
    {
        let level = asg.level_ref();
        unsafe {
            let key: usize = self.lbd_temp.get_unchecked(0) + 1;
            *self.lbd_temp.get_unchecked_mut(0) = key;
            let mut cnt = 0;
            for l in vec {
                let lv = level[l.vi()];
                let p = self.lbd_temp.get_unchecked_mut(lv as usize);
                if *p != key {
                    *p = key;
                    cnt += 1;
                }
            }
            cnt
        }
    }
    fn compute_lbd_of<A>(&mut self, asg: &A, cid: ClauseId) -> usize
    where
        A: AssignIF,
    {
        let level = asg.level_ref();
        unsafe {
            let key: usize = self.lbd_temp.get_unchecked(0) + 1;
            *self.lbd_temp.get_unchecked_mut(0) = key;
            let mut cnt = 0;
            for l in &self.clause[cid.ordinal as usize].lits {
                let lv = level[l.vi()];
                let p = self.lbd_temp.get_unchecked_mut(lv as usize);
                if *p != key {
                    *p = key;
                    cnt += 1;
                }
            }
            cnt
        }
    }
    fn reset_lbd<A>(&mut self, asg: &A, all: bool)
    where
        A: AssignIF,
    {
        let level = asg.level_ref();
        let mut key = self.lbd_temp[0];
        for c in &mut self.clause.iter_mut().skip(1) {
            if c.is(Flag::DEAD) || !c.is(Flag::LEARNT) || (!all && !c.is(Flag::JUST_USED)) {
                continue;
            }
            key += 1;
            let mut cnt = 0;
            for l in &c.lits {
                let lv = level[l.vi()];
                if lv != 0 {
                    let p = unsafe { self.lbd_temp.get_unchecked_mut(lv as usize) };
                    if *p != key {
                        *p = key;
                        cnt += 1;
                    }
                }
            }
            c.rank = cnt;
        }
        self.lbd_temp[0] = key;
        self.num_lbd_update += 1;
    }
}

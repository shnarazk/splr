use {
    super::ClauseDB,
    crate::{assign::AssignIF, types::*},
};

/// API to calculate LBD.
pub trait LBDIF {
    /// return the LBD value for a set of literals.
    fn compute_lbd<A>(&mut self, asg: &A, vec: &[Lit]) -> usize
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
}

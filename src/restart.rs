use solver::*;
use std::cmp::min;
use types::*;

pub trait Restart {
    fn should_restart(&mut self, lbd: usize, clv: usize) -> bool;
}

impl Restart for Solver {
    /// renamed from checkRestartCondition
    fn should_restart(&mut self, lbd: usize, clv: usize) -> bool {
        let next: u64 = self.next_restart;
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        let nas = self.num_assigns() as f64;
        let b_l = self.decision_level() as f64;
        let d_f = self.lbd_f.update(lbd as f64);
        let d_s = self.lbd_s.update(lbd as f64);
        let a_f = self.asg_f.update(nas);
        let a_s = self.asg_s.update(nas);
        let c_v = self.c_lvl.update(clv as f64);
        let n_b = self.stats[Stat::NumOfBlockRestart as usize];
        let n_f = self.stats[Stat::NumOfRestart as usize];
        let should_block = 1.20 * a_s < a_f;
        let should_force = 1.15 * d_s < d_f;
        if count < next {
            self.b_lvl.update(b_l);
            false
        } else if should_block && !should_force {
            self.stats[Stat::NumOfBlockRestart as usize] += 1;
            self.next_restart = count + c_v.powf(2.0) as u64;
            self.b_lvl.update(b_l);
            false
        } else if !should_block && should_force {
            self.stats[Stat::NumOfRestart as usize] += 1;
            self.next_restart = count + (1.5 * c_v) as u64;
            self.b_lvl.update(0.0);
            true
        } else {
            self.next_restart = count + (1.5 * c_v) as u64;
            self.b_lvl.update(b_l);
            false
        }
    }
}

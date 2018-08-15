use solver::*;
use types::*;

pub trait Restart {
    fn should_restart(&mut self, lbd: usize, clv: usize) -> bool;
}

impl Restart for Solver {
    /// renamed from checkRestartCondition
    fn should_restart(&mut self, lbd: usize, clv: usize) -> bool {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        let nas = self.num_assigns() as f64;
        let b_l = self.decision_level() as f64;
        let e_asg = self.ema_asg.update(nas);
        let e_lbd = self.ema_lbd.update(lbd as f64);
        let c_v = self.c_lvl.update(clv as f64);
        let should_block = 1.5 < e_asg;
        let should_force = 1.5 < e_lbd;
        if count < self.check_restart {
            self.b_lvl.update(b_l);
            false
        } else if should_force {
            self.next_restart = count + 400;
            self.check_restart = count + 200; // (1.5 * c_v) as u64;
            println!("forcing {:.2} {:.2}", e_lbd, c_v);
            self.stats[Stat::NumOfRestart as usize] += 1;
            self.b_lvl.update(0.0);
            true
        } else if count < self.next_restart {
            self.check_restart = self.next_restart;
            self.b_lvl.update(b_l);
            false
        } else if should_block {
            self.next_restart = count + 1000 + ((c_v.powf(2.0)) as u64);
            self.check_restart = count + 1000;
            println!("blocking {:.2} {:.2}", e_asg, c_v);
            self.stats[Stat::NumOfBlockRestart as usize] += 1;
            self.b_lvl.update(b_l);
            false
        } else {
            let p = self.stats[Stat::NumOfRestart as usize] as f64;
            let e: f64 = 1.05;
            self.next_restart = count + 400 + 100 * (e.powf(p) as u64);
            self.check_restart = count + 200;
            self.stats[Stat::NumOfRestart as usize] += 1;
            self.b_lvl.update(0.0);
            true
        }
    }
}

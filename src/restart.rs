use solver::{Solver, Stat};
use types::*;
use solver::CDCL;

pub trait Restart {
    fn block_restart(&mut self, lbd: usize, clv: usize, blv: usize, nas: usize) -> ();
    fn force_restart(&mut self) -> ();
}

const RESTART_PERIOD: u64 = 50;
const RESTART_PROHIBIT: u64 = 45;
/// for block restart based on average assigments: 1.40
const R: f64 = 1.6;
/// for force restart based on average LBD of newly generated clauses: 1.15
const K: f64 = 1.8;

impl Restart for Solver {

    /// called after conflict resolution
    fn block_restart(&mut self, lbd: usize, clv: usize, blv: usize, nas: usize) -> () {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        self.ema_asg.update(nas as f64);
        self.ema_lbd.update(lbd as f64);
        self.c_lvl.update(clv as f64);
        self.b_lvl.update(blv as f64);
        // if count == RESTART_PROHIBIT {
        //     self.ema_asg.reset();
        //     self.ema_lbd.reset();
        //     self.c_lvl.reset();
        //     self.b_lvl.reset();
        // }
        if self.next_restart <= count && 0 < lbd && R < self.ema_asg.get() {
            self.next_restart = count + RESTART_PERIOD;
            self.stats[Stat::NumOfBlockRestart as usize] += 1;
            // self.ema_lbd.reset();
        }
        // println!("block_restart count {}, next {} {}", count, self.next_restart, R < self.ema_asg.get());
    }

    /// called after no conflict propagation
    fn force_restart(&mut self) -> () {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        if self.next_restart < count && K < self.ema_lbd.get() {
            self.next_restart = count + RESTART_PERIOD;
            self.stats[Stat::NumOfRestart as usize] += 1;
            let rl = self.root_level;
            self.cancel_until(rl);
        }
    }
}

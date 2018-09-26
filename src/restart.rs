use solver::{Solver, Stat, CDCL};
use types::*;

pub trait Restart {
    fn block_restart(&mut self, lbd: usize, clv: usize, blv: usize, nas: usize) -> ();
    fn force_restart(&mut self) -> ();
}

/// for block restart based on average assigments: 1.40
const R: f64 = 1.60;
const RR: f64 = 0.85;

/// for force restart based on average LBD of newly generated clauses: 1.15
const K: f64 = 1.48;

const RESTART_PERIOD: u64 = 50;
const RESET_EMA: u64 = 50;

impl Restart for Solver {
    /// called after conflict resolution
    fn block_restart(&mut self, lbd: usize, clv: usize, blv: usize, nas: usize) -> () {
        let nv = self.num_vars;
        let count = self.stat[Stat::Conflict as usize] as u64;
        self.c_lvl.update(clv as f64);
        self.b_lvl.update(blv as f64);
        self.ema_asg.update((nv - nas) as f64);
        self.ema_lbd.update(lbd as f64);
        if count == RESET_EMA {
            self.ema_asg.reset();
            self.ema_lbd.reset();
            self.c_lvl.reset();
            self.b_lvl.reset();
        }
        if self.next_restart <= count && self.ema_asg.get() < RR {
            self.next_restart = count + RESTART_PERIOD;
            self.stat[Stat::BlockRestart as usize] += 1;
        }
    }

    /// called after no conflict propagation
    fn force_restart(&mut self) -> () {
        let count = self.stat[Stat::Conflict as usize] as u64;
        if self.next_restart < count && K < self.ema_lbd.get() {
            self.next_restart = count + RESTART_PERIOD;
            self.stat[Stat::Restart as usize] += 1;
            let rl = self.root_level;
            self.cancel_until(rl);
        }
    }
}

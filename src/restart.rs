// use clause::ClauseManagement;
use crate::solver::{Solver, Stat, CDCL};
use crate::types::*;
use std::collections::VecDeque;

// for VecDeque<usize>
pub trait QueueOperations {
    fn average(&self) -> f64;
    fn enqueue(&mut self, x: usize) -> bool;
    fn is_full(&self) -> bool;
}

// for Solver
pub trait Restart {
    fn block_restart(&mut self, lbd: usize, clv: usize, blv: usize, nas: usize) -> ();
    fn force_restart(&mut self) -> ();
}

/// for block restart based on average assigments: 1.40
pub const R: f64 = 1.4;

/// for force restart based on average LBD of newly generated clauses: 1.15
pub const K: f64 = 0.8;

const RESTART_PERIOD: u64 = 50;
const RESET_EMA: u64 = 1000;

impl QueueOperations for VecDeque<usize> {
    fn average(&self) -> f64 {
        let len = self.len() as f64;
        let sum = self.iter().sum::<usize>() as f64;
        sum / len
    }
    fn enqueue(&mut self, x: usize) -> bool {
        self.push_back(x);
        if 50 < self.len() {
            self.pop_front();
            true
        } else {
            50 == self.len()
        }
    }
    fn is_full(&self) -> bool {
        50 <= self.len()
    }
}

impl Restart for Solver {
    /// called after conflict resolution
    fn block_restart(&mut self, lbd: usize, clv: usize, blv: usize, nas: usize) -> () {
        let count = self.stat[Stat::Conflict as usize] as u64;
        self.c_lvl.update(clv as f64);
        self.b_lvl.update(blv as f64);
        self.ema_asg.update(nas as f64);
        self.ema_lbd.update(lbd as f64);
        if count <= RESET_EMA {
            if count == RESET_EMA {
                self.ema_asg.reset();
                self.ema_lbd.reset();
                self.c_lvl.reset();
                self.b_lvl.reset();
            }
            return;
        }
        if self.next_restart <= count && R < self.ema_asg.get() {
            self.next_restart = count + RESTART_PERIOD;
            self.stat[Stat::BlockRestart as usize] += 1;
        }
    }

    /// called after no conflict propagation
    fn force_restart(&mut self) -> () {
        let count = self.stat[Stat::Conflict as usize] as u64;
        if RESET_EMA < count && self.next_restart < count && K < self.ema_lbd.get() {
            self.next_restart = count + RESTART_PERIOD;
            self.stat[Stat::Restart as usize] += 1;
            let rl = self.root_level;
            self.cancel_until(rl);
        }
    }
}

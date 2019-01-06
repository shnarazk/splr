use crate::solver::Solver;
use crate::state::Stat;
use crate::types::*;
use std::collections::VecDeque;

/// For VecDeque<usize>
pub trait QueueOperations {
    fn average(&self) -> f64;
    fn enqueue(&mut self, lim: usize, x: usize) -> bool;
    fn is_full(&self, lim: usize) -> bool;
}

/// For Solver
pub trait Restart {
    fn block_restart(&mut self, lbd: usize, clv: usize, blv: usize, nas: usize) -> ();
    fn force_restart(&mut self) -> ();
}

/// For force restart based on average LBD of newly generated clauses: 1.15.
/// This is called `K` in Glusoce
pub const RESTART_THR: f64 = 0.8;

/// For block restart based on average assigments: 1.40.
/// This is called `R` in Glucose
pub const RESTART_BLK: f64 = 1.40;

const RESTART_PERIOD: u64 = 50;
const RESET_EMA: u64 = 1000;

impl QueueOperations for VecDeque<usize> {
    #[inline(always)]
    fn average(&self) -> f64 {
        // let len = self.len() as f64;
        // let sum = self.iter().sum::<usize>() as f64;
        // sum / len
        (self.iter().sum::<usize>() as f64) / (self.len() as f64)
    }
    #[inline(always)]
    fn enqueue(&mut self, lim: usize, x: usize) -> bool {
        self.push_back(x);
        if lim < self.len() {
            self.pop_front();
            true
        } else {
            lim == self.len()
        }
    }
    #[inline(always)]
    fn is_full(&self, lim: usize) -> bool {
        lim <= self.len()
    }
}

impl Restart for Solver {
    /// called after conflict resolution
    fn block_restart(&mut self, lbd: usize, clv: usize, blv: usize, nas: usize) {
        let count = self.state.stats[Stat::Conflict as usize] as u64;
        self.state.c_lvl.update(clv as f64);
        self.state.b_lvl.update(blv as f64);
        self.state.ema_asg.update(nas as f64);
        self.state.ema_lbd.update(lbd as f64);
        if count <= RESET_EMA {
            if count == RESET_EMA {
                self.state.ema_asg.reset();
                self.state.ema_lbd.reset();
                self.state.c_lvl.reset();
                self.state.b_lvl.reset();
            }
            return;
        }
        if self.state.next_restart <= count && self.config.restart_blk < self.state.ema_asg.get() {
            self.state.next_restart = count + RESTART_PERIOD;
            self.state.stats[Stat::BlockRestart as usize] += 1;
        }
    }

    /// called after no conflict propagation
    fn force_restart(&mut self) {
        let Solver {
            ref mut asgs,
            ref mut config,
            ref mut state,
            ref mut vars,
            ..
        } = self;
        let count = state.stats[Stat::Conflict as usize] as u64;
        if RESET_EMA < count
            && state.next_restart < count
            && config.restart_thr < state.ema_lbd.get()
        {
            state.next_restart = count + RESTART_PERIOD;
            state.stats[Stat::Restart as usize] += 1;
            asgs.cancel_until(vars, &mut state.var_order, config.root_level);
        }
    }
}

pub fn luby(y: f64, mut x: usize) -> f64 {
    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    let mut size: usize = 1;
    let mut seq: usize = 0;
    // for(size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1);
    // while(size - 1 != x) {
    //     size = (size - 1) >> 1;
    //     seq--;
    //     x = x % size;
    // }
    // return pow(y, seq);
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    // while(size - 1 != x) {
    //     size = (size - 1) >> 1;
    //     seq--;
    //     x = x % size;
    // }
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    y.powf(seq as f64)
}

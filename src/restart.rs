use crate::assign::AssignStack;
use crate::config::SolverConfig;
use crate::state::{SolverState, Stat};
use crate::traits::*;
use std::collections::VecDeque;

const RESTART_PERIOD: u64 = 50;
const RESET_EMA: u64 = 400;

impl QueueOperations for VecDeque<usize> {
    #[inline(always)]
    fn average(&self) -> f64 {
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

impl Restart for SolverConfig {
    /// called after conflict resolution
    fn block_restart(
        &mut self,
        asgs: &AssignStack,
        state: &mut SolverState,
        lbd: usize,
        blv: usize,
    ) -> bool {
        let count = state.stats[Stat::Conflict as usize] as u64;
        let nas = asgs.len();
        let clv = asgs.level();
        state.c_lvl.update(clv as f64);
        state.b_lvl.update(blv as f64);
        state.ema_asg.update(nas as f64);
        state.ema_lbd.update(lbd as f64);
        if count <= RESET_EMA {
            if count == RESET_EMA {
                state.ema_asg.reset();
                state.ema_lbd.reset();
                state.c_lvl.reset();
                state.b_lvl.reset();
            }
            return false;
        }
        if state.next_restart <= count && self.restart_blk < state.ema_asg.get() {
            state.next_restart = count + RESTART_PERIOD;
            return true;
        }
        false
    }

    /// called after no conflict propagation
    fn force_restart(&mut self, state: &mut SolverState) -> bool {
        let count = state.stats[Stat::Conflict as usize] as u64;
        if RESET_EMA < count
            && state.next_restart < count
            && 1.0 / state.ema_lbd.get() < self.restart_thr
        {
            state.next_restart = count + RESTART_PERIOD;
            return true;
        }
        false
    }
}

pub fn luby(y: f64, mut x: usize) -> f64 {
    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    let mut size: usize = 1;
    let mut seq: usize = 0;
    // for(size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1);
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
    // return pow(y, seq);
    y.powf(seq as f64)
}

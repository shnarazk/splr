use crate::assign::AssignStack;
use crate::config::SolverConfig;
use crate::state::{SolverState, Stat};
use crate::traits::*;
use std::collections::VecDeque;

const RESTART_PERIOD: u64 = 50;
const RESET_EMA: u64 = 400;
const LBD_QUEUE_LEN: usize = 50;
const TRAIL_QUEUE_LEN: usize = 5000;

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

impl RestartIF for SolverState {
    /// called after conflict resolution
    fn block_restart(&mut self, asgs: &AssignStack, config: &SolverConfig, ncnfl: usize) -> bool {
        let count = self.stats[Stat::Conflict as usize] as u64;
        let nas = asgs.len();
        let clv = asgs.level();
        if count <= RESET_EMA {
            if count == RESET_EMA {
                self.ema_asg.reset();
                self.ema_lbd.reset();
            }
            return false;
        }
        if 100 < ncnfl
            && self.lbd_queue.is_full(LBD_QUEUE_LEN)
            && config.restart_blk * self.trail_queue.average() < (nas as f64)
        {
            self.lbd_queue.clear();
            self.stats[Stat::BlockRestart as usize] += 1;
            return true;
        } else {
            return false;
        }
        // if self.next_restart <= count && self.restart_blk < self.ema_asg.get() {
        if self.next_restart <= count && config.restart_blk * self.ema_asg.fast < nas as f64 {
            self.next_restart = count + RESTART_PERIOD;
            return true;
        }
        false
    }
    /// called after no conflict propagation
    fn force_restart(&mut self, config: &mut SolverConfig, ncnfl: &mut f64) -> bool {
        let count = self.stats[Stat::Conflict as usize] as u64;
        let ave = self.stats[Stat::SumLBD as usize] as f64 / count as f64;
        if (config.luby_restart && config.luby_restart_num_conflict <= *ncnfl)
            || (!config.luby_restart
                && self.lbd_queue.is_full(LBD_QUEUE_LEN)
                && ((self.stats[Stat::SumLBD as usize] as f64)
                    / (self.stats[Stat::Conflict as usize] as f64)
                    < self.lbd_queue.average() * config.restart_thr))
        {
            self.stats[Stat::Restart as usize] += 1;
            self.lbd_queue.clear();
            if config.luby_restart {
                *ncnfl = 0.0;
                config.luby_current_restarts += 1;
                config.luby_restart_num_conflict =
                    luby(config.luby_restart_inc, config.luby_current_restarts)
                        * config.luby_restart_factor;
                // println!("luby restart {}", luby_restart_num_conflict);
                // return
            }
            return true;
        } else {
            return false;
        }
        if RESET_EMA < count
            && self.next_restart < count
            && ave < self.ema_lbd.fast * config.restart_thr
        // && 1.0 / self.ema_lbd.get() < config.restart_thr
        {
            self.next_restart = count + RESTART_PERIOD;
            return true;
        }
        false
    }
    #[inline(always)]
    fn restart_update_lbd(&mut self, lbd: usize) {
        self.ema_lbd.update(lbd as f64);
        self.lbd_queue.enqueue(LBD_QUEUE_LEN, lbd);
    }
    #[inline(always)]
    fn restart_update_asg(&mut self, n: usize) {
        self.ema_asg.update(n as f64);
        self.trail_queue.enqueue(TRAIL_QUEUE_LEN, n);
    }
    #[inline(always)]
    fn restart_update_luby(&mut self, config: &mut SolverConfig) {
        if config.luby_restart {
            config.luby_restart_num_conflict =
                luby(config.luby_restart_inc, config.luby_current_restarts)
                    * config.luby_restart_factor;
        }
    }
}

fn luby(y: f64, mut x: usize) -> f64 {
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

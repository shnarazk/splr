use crate::assign::AssignStack;
use crate::config::SolverConfig;
use crate::state::{SolverState, Stat};
use crate::traits::*;

const RESTART_PERIOD: usize = 50;
const RESET_EMA: usize = 400;

impl RestartIF for SolverState {
    fn block_restart(&mut self, asgs: &AssignStack, config: &SolverConfig, ncnfl: usize) -> bool {
        let nas = asgs.len();
        if 100 < ncnfl
            && RESTART_PERIOD <= self.after_restart
            && config.restart_blk * self.ema_asg.fast < nas as f64
        {
            self.after_restart = 0;
            self.stats[Stat::BlockRestart as usize] += 1;
            return true;
        }
        false
    }
    fn force_restart(&mut self, config: &mut SolverConfig, ncnfl: &mut f64) -> bool {
        let count = self.stats[Stat::Conflict as usize] as usize;
        if count <= RESET_EMA {
            if count == RESET_EMA {
                self.ema_asg.reset();
                self.ema_lbd.reset();
            }
            return false;
        }
        let ave = self.stats[Stat::SumLBD as usize] as f64 / count as f64;
        if (config.luby_restart && config.luby_restart_num_conflict <= *ncnfl)
            || (!config.luby_restart
                && RESTART_PERIOD <= self.after_restart
                && ave < self.ema_lbd.fast * config.restart_thr
            )
        {
            self.stats[Stat::Restart as usize] += 1;
            self.after_restart = 0;
            if config.luby_restart {
                *ncnfl = 0.0;
                config.luby_current_restarts += 1;
                config.luby_restart_num_conflict =
                    luby(config.luby_restart_inc, config.luby_current_restarts)
                        * config.luby_restart_factor;
            }
            return true;
        }
        false
    }
    #[inline(always)]
    fn restart_update_lbd(&mut self, lbd: usize) {
        self.ema_lbd.update(lbd as f64);
        self.after_restart += 1;
    }
    #[inline(always)]
    fn restart_update_asg(&mut self, n: usize) {
        self.ema_asg.update(n as f64);
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

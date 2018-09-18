use clause::ClauseIdIndexEncoding;
use clause::ClauseFlag;
use solver::{Solver, Stat};
use types::*;
use var::VarOrdering;

pub trait Restart {
    fn cancel_until(&mut self, lv: usize) -> ();
    fn force_restart(&mut self) -> ();
    fn block_restart(&mut self, lbd: usize, clv: usize) -> ();
}

const RESTART_PERIOD: u64 = 50;
const RESTART_PROHIBIT: u64 = 40;
/// for block restart based on average assigments: 1.40
const R: f64 = 1.02;
/// for force restart based on average LBD of newly generated clauses: 1.15
const K: f64 = 1.28;

impl Restart for Solver {
    fn cancel_until(&mut self, lv: usize) -> () {
        if self.decision_level() <= lv {
            return;
        }
        let lim = self.trail_lim[lv];
        for l in &self.trail[lim..] {
            let vi = l.vi();
            {
                let v = &mut self.vars[vi];
                v.phase = v.assign;
                v.assign = BOTTOM;
                if 0 < v.reason {
                    self.cp[v.reason.to_kind()].clauses[v.reason.to_index()].set_flag(ClauseFlag::Locked, false);
                }
                v.reason = NULL_CLAUSE;
            }
            self.var_order.insert(&self.vars, vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(lv);
        self.q_head = lim;
    }
    /// called after no conflict propagation
    fn force_restart(&mut self) -> () {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        let nas = self.num_assigns() as f64;
        self.ema_asg.update(nas);
        let should_force = K < self.ema_lbd.get();
        if count <= RESTART_PROHIBIT {
            if count == RESTART_PROHIBIT {
                self.ema_asg.reset();
                self.ema_lbd.reset();
                self.c_lvl.reset();
                self.b_lvl.reset();
            }
            return;
        }
        if self.next_restart < count && should_force {
            self.next_restart = count + RESTART_PERIOD;
            self.stats[Stat::NumOfRestart as usize] += 1;
            let rl = self.root_level;
            self.cancel_until(rl);
        }
    }
    /// called after conflict resolution
    fn block_restart(&mut self, lbd: usize, clv: usize) -> () {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        let dl = self.decision_level() as f64;
        self.b_lvl.update(dl);
        self.c_lvl.update(clv as f64);
        self.ema_lbd.update(lbd as f64);
        if count <= RESTART_PROHIBIT {
            if count == RESTART_PROHIBIT {
                self.ema_asg.reset();
                self.ema_lbd.reset();
                self.c_lvl.reset();
                self.b_lvl.reset();
            }
            return;
        }
        let should_block = R < self.ema_asg.get();
        if self.next_restart <= count && should_block {
            self.next_restart = count + RESTART_PERIOD;
            self.stats[Stat::NumOfBlockRestart as usize] += 1;
        }
    }
}

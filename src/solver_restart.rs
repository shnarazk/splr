use assign::Assignment;
use solver::SatSolver;
use solver_propagate::SolveSAT;
use solver::{Solver, Stat};
use types::*;

/// for Solver
pub trait Restart {
    fn force_restart(&mut self) -> ();
    fn block_restart(&mut self, lbd: usize, clv: usize) -> ();
}

const RESTART_PERIOD: u64 = 40;
/// for block restart based on average assingments: 1.40
const R: f64 = 1.40;
/// for force restart based on average LBD of newly generated clauses: 1/0.8
const K: f64 = 1.25;

const SAMPLING_TIME: u64 = 1000;

impl Restart for Solver {
    /// called after no conflict propagation
   ///```C
   ///            // Our dynamic restart, see the SAT09 competition compagnion paper
   ///            if((luby_restart && nof_conflicts <= conflictC) ||
   ///               (!luby_restart && (lbdQueue.isvalid() && ((lbdQueue.getavg() * K) > (sumLBD / conflictsRestarts))))) {
   ///                lbdQueue.fastclear();
   ///```
    fn force_restart(&mut self) -> () {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        if count < SAMPLING_TIME {
            return;
        } else if count == SAMPLING_TIME {
            self.ema_lbd.reset();
            self.ema_asg.reset();
            self.c_lvl.reset();
            return;
        } else if count == SAMPLING_TIME * 10 {
            self.ema_lbd.reset();
            self.ema_asg.reset();
            self.c_lvl.reset();
            return;
        }
        let e_lbd = self.ema_lbd.get();
        let _c_lvl = self.c_lvl.get();
        // let b_lvl = self.b_lvl.get();
        let should_force = K < e_lbd;
        if self.next_restart <= count && should_force {
            self.next_restart = count + RESTART_PERIOD;
            self.stats[Stat::NumOfRestart as usize] += 1;
            let rl = self.root_level;
            self.cancel_until(rl);
            // println!(" - {:.2} {:.2}", cnt, e_lbd);
        }
    }
    /// called after conflict resolution
    ///```C
    /// #define LOWER_BOUND_FOR_BLOCKING_RESTART SAMPLING_TIME
    ///
    ///            trailQueue.push(trail.size());
    ///            // BLOCK RESTART (CP 2012 paper)
    ///            if(conflictsRestarts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && trail.size() > R * trailQueue.getavg()) {
    ///                lbdQueue.fastclear();
    ///                cancelUntil(0);
    ///```
    fn block_restart(&mut self, lbd: usize, clv: usize) -> () {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        let nas = self.num_assigns() as f64;
        let b_l = self.am.decision_level() as f64;
        self.ema_asg.update(nas);
        let e_asg = self.ema_asg.get();
        self.ema_lbd.update(lbd as f64);
        let _e_lbd = self.ema_lbd.get();
        self.c_lvl.update(clv as f64);
        let c_lvl = self.c_lvl.get();
        self.b_lvl.update(b_l);
        if count < SAMPLING_TIME {
            return;
        } else if count == SAMPLING_TIME {
            self.ema_lbd.reset();
            self.ema_asg.reset();
            self.c_lvl.reset();
            return;
        } else if count == SAMPLING_TIME * 10 {
            self.ema_lbd.reset();
            self.ema_asg.reset();
            self.c_lvl.reset();
            return;
        }
        let should_block = R < e_asg / c_lvl;
        if self.next_restart <= count && should_block {
            self.next_restart = count + RESTART_PERIOD;
            self.stats[Stat::NumOfBlockRestart as usize] += 1;
            // println!("blocking {:.2} {:.2}", e_asg, self.stats[Stat::NumOfBlockRestart as usize]);
        }
    }
}

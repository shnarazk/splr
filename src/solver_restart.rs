use solver::{Solver, Stat};
use types::*;
use solver::SatSolver;
use solver_propagate::SolveSAT;

pub trait Restart {
    fn force_restart(&mut self) -> ();
    fn block_restart(&mut self, lbd: usize, clv: usize) -> ();
}

const RESTART_PERIOD: u64 = 60;
/// for block restart based on average assingments: 1.40
const R: f64 = 1.1;
/// for force restart based on average LBD of newly generated clauses: 1.15
const K: f64 = 1.4; // 1.0 / 0.8

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
        let e_lbd = self.ema_lbd.get();
        let should_force = K < e_lbd;
        if self.next_restart < count && should_force {
            self.next_restart = count + RESTART_PERIOD;
            self.stats[Stat::NumOfRestart as usize] += 1;
            let rl = self.root_level;
            self.cancel_until(rl);
            // println!(" - {:.2} {:.2}", cnt, e_lbd);
        }
    }
    /// called after conflict resolution
    ///```C
    /// #define LOWER_BOUND_FOR_BLOCKING_RESTART 10000
    ///
    ///            // BLOCK RESTART (CP 2012 paper)
    ///            if(conflictsRestarts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && trail.size() > R * trailQueue.getavg()) {
    ///                lbdQueue.fastclear();
    ///                cancelUntil(0);
    ///```
    fn block_restart(&mut self, lbd: usize, clv: usize) -> () {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        let nas = self.num_assigns() as f64;
        let b_l = self.decision_level() as f64;
        self.ema_asg.update(nas);
        let e_asg = self.ema_asg.get();
        self.ema_lbd.update(lbd as f64);
        let _e_lbd = self.ema_lbd.get();
        self.c_lvl.update(clv as f64);
        self.b_lvl.update(b_l);
        let should_block = R < e_asg;
        if 4000 < count && self.next_restart <= count && should_block {
            self.next_restart = count + RESTART_PERIOD;
            self.stats[Stat::NumOfBlockRestart as usize] += 1;
            // println!("blocking {:.2} {:.2}", e_asg, self.stats[Stat::NumOfBlockRestart as usize]);
        }
    }
}

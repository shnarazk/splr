use solver::{Solver, Stat};
use types::*;
use var::VarOrdering;

pub trait Restart {
    fn cancel_until(&mut self, lv: usize) -> ();
    fn force_restart(&mut self) -> ();
    fn block_restart(&mut self, lbd: usize, clv: usize) -> ();
}

impl Restart for Solver {
    fn cancel_until(&mut self, lv: usize) -> () {
        let dl = self.decision_level();
        if dl <= lv {
            return;
        }
        let lim = self.trail_lim[lv];
        for l in &self.trail[lim..] {
            let vi = l.vi();
            {
                let v = &mut self.vars[vi];
                if v.level == dl {
                    v.phase = v.assign;
                }
                v.assign = BOTTOM;
                if 0 < v.reason {
                    self.clauses[v.reason].locked = false;
                }
                v.reason = NULL_CLAUSE;
            }
            self.var_order.insert(&self.vars, vi);
        }
        self.trail.truncate(lim); // FIXME
        self.trail_lim.truncate(lv);
        self.q_head = lim;
        // self.dump("cancel_until");
    }
    fn force_restart(&mut self) -> () {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        let e_lbd = self.ema_lbd.get();
        let _c_v = self.c_lvl.get();
        let should_force = 1.0 / 0.90 < e_lbd;
        if !(count < self.check_restart) && should_force {
            self.next_restart = count + 50;
            self.check_restart = count + 50; // (1.5 * c_v) as u64;
            self.stats[Stat::NumOfRestart as usize] += 1;
            // println!("forcing {:.2} {:.2}", e_lbd, self.stats[Stat::NumOfRestart as usize]);
            let rl = self.root_level;
            self.cancel_until(rl);
        }
    }
    fn block_restart(&mut self, lbd: usize, clv: usize) -> () {
        let count = self.stats[Stat::NumOfBackjump as usize] as u64;
        let nas = self.num_assigns() as f64;
        let b_l = self.decision_level() as f64;
        let e_asg = self.ema_asg.update(nas);
        let _e_lbd = self.ema_lbd.update(lbd as f64);
        let _c_v = self.c_lvl.update(clv as f64);
        let should_block = 1.1 < e_asg;
        self.b_lvl.update(b_l);
        if !(count < self.check_restart) && should_block {
            self.next_restart = count + 50; // 1000 + ((c_v.powf(2.0)) as u64);
            self.check_restart = count + 50;
            self.stats[Stat::NumOfBlockRestart as usize] += 1;
            // println!("blocking {:.2} {:.2}", e_asg, self.stats[Stat::NumOfBlockRestart as usize]);
        }
    }
}

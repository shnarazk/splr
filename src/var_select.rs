use solver::*;
use types::*;

pub trait VarSelection {
    fn bump_vi(&mut self, vi: VarIndex) -> ();
    fn decay_var_activity(&mut self) -> ();
}

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;

impl VarSelection for Solver {
    fn bump_vi(&mut self, vi: VarIndex) -> () {
        let d = self.stats[StatIndex::NumOfBackjump as usize] as f64;
        let a = (self.vars[vi].activity + d) / 2.0;
        self.vars[vi].activity = a;
        if VAR_ACTIVITY_THRESHOLD < a {
            self.rescale_var_activity();
        }
        self.var_order.update(&self.vars, vi);
    }
    fn decay_var_activity(&mut self) -> () {
        self.var_inc = self.var_inc / VAR_ACTIVITY_THRESHOLD;
    }
}

impl Solver {
    fn rescale_var_activity(&mut self) -> () {
        for i in 1..self.vars.len() {
            self.vars[i].activity = self.vars[i].activity / VAR_ACTIVITY_THRESHOLD;
        }
        self.var_inc /= VAR_ACTIVITY_THRESHOLD;
    }
}

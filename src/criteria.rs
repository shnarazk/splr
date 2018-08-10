use clause::*;
use solver::*;
use std::cmp::max;
use std::cmp::min;
use types::*;

const VAR_ACTIVITY_THRESHOLD: f64 = 1e100;
const CLAUSE_ACTIVITY_THRESHOLD: f64 = 1e20;

impl Solver {
    pub fn bump_ci(&mut self, ci: ClauseIndex) -> () {
        if ci <= 0 {
            return;
        }
        let a = self.learnts[ci as usize].activity + self.cla_inc;
        self.learnts[ci as usize].activity = a;
        if CLAUSE_ACTIVITY_THRESHOLD < a {
            self.rescale_clause_activity()
        }
    }
    pub fn decay_cla_activity(&mut self) -> () {
        self.cla_inc = self.cla_inc / CLAUSE_ACTIVITY_THRESHOLD;
    }
    pub fn rescale_clause_activity(&mut self) -> () {
        for i in 1..self.learnts.len() {
            self.learnts[i].activity = self.learnts[i].activity / CLAUSE_ACTIVITY_THRESHOLD;
        }
        self.cla_inc /= CLAUSE_ACTIVITY_THRESHOLD;
    }
    pub fn bump_vi(&mut self, vi: VarIndex) -> () {
        let d = self.stats[StatIndex::NumOfBackjump as usize] as f64;
        let a = (self.vars[vi].activity + d) / 2.0;
        self.vars[vi].activity = a;
        if VAR_ACTIVITY_THRESHOLD < a {
            self.rescale_var_activity();
        }
        self.var_order.update(&self.vars, vi);
    }
    pub fn decay_var_activity(&mut self) -> () {
        self.var_inc = self.var_inc / VAR_ACTIVITY_THRESHOLD;
    }
    pub fn rescale_var_activity(&mut self) -> () {
        for i in 1..self.vars.len() {
            self.vars[i].activity = self.vars[i].activity / VAR_ACTIVITY_THRESHOLD;
        }
        self.var_inc /= VAR_ACTIVITY_THRESHOLD;
    }
    // renamed from clause_new
    pub fn add_clause(&mut self, learnt: bool, mut v: Vec<Lit>) -> bool {
        assert_eq!(learnt, false);
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means totology.
        let mut result = false;
        for i in 0..v.len() {
            let li = v[i];
            let sat = self.assigned(li);
            if sat == LTRUE || li.negate() == l_ {
                v.clear();
                result = true;
                break;
            } else if sat != LFALSE && li != l_ {
                v[j] = li;
                j += 1;
                l_ = li;
            }
        }
        if result != true {
            v.truncate(j)
        }
        match v.len() {
            0 => result,
            1 => self.enqueue(v[0], NULL_CLAUSE),
            _ => {
                self.inject(false, Clause::new(v));
                true
            }
        }
    }
    pub fn lbd_of(&mut self, v: &Vec<Lit>) -> usize {
        let k = 1 + self.lbd_key;
        self.lbd_key = k;
        if 1000_000 < k {
            self.lbd_key = 0;
        }
        let n = v.len();
        let mut cnt = 0;
        for i in 0..n {
            let l = self.vars[v[i].vi()].level;
            if self.lbd_seen[l] != k && l != 0 {
                self.lbd_seen[l] = k;
                cnt += 1;
            }
        }
        max(1, cnt)
    }
    /// renamed from checkRestartCondition
    pub fn should_restart(&mut self, lbd: usize, clv: usize) -> bool {
        let next: u64 = self.next_restart;
        let count = self.stats[StatIndex::NumOfBackjump as usize] as u64;
        let nas = self.num_assigns() as f64;
        let b_l = self.decision_level() as f64;
        let d_f = self.lbd_f.update(lbd as f64);
        let d_s = self.lbd_s.update(lbd as f64);
        let a_f = self.asg_f.update(nas);
        let a_s = self.asg_s.update(nas);
        let c_v = self.c_lvl.update(clv as f64);
        let n_b = self.stats[StatIndex::NumOfBlockRestart as usize];
        let n_f = self.stats[StatIndex::NumOfRestart as usize];
        let bias = if min(n_b, n_f) < 4 {
            1.25
        } else if n_b <= n_f {
            1.25 + (n_f as f64 / n_b as f64).powf(2.0)
        } else {
            1.25 - (n_f as f64 / n_b as f64).powf(2.0)
        };
        if count < next {
            self.b_lvl.update(b_l);
            false
        } else if 1.25 * a_s < a_f {
            self.stats[StatIndex::NumOfBlockRestart as usize] += 1;
            self.next_restart = count + c_v.powf(2.0) as u64;
            self.b_lvl.update(b_l);
            false
        } else if bias * d_s < d_f {
            self.stats[StatIndex::NumOfRestart as usize] += 1;
            self.next_restart = count + (1.5 * c_v) as u64;
            self.b_lvl.update(0.0);
            true
        } else {
            self.next_restart = count + (1.5 * c_v) as u64;
            self.b_lvl.update(b_l);
            false
        }
    }
}

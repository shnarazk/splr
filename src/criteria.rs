#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
use clause::*;
use solver::*;
use std::cmp::max;
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
        let d = self.get_stat(&StatIndex::NumOfBackjump) as f64;
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
    fn clause_new(&mut self, learnt: bool, v: &mut Vec<Lit>) -> Result<ClauseIndex, bool> {
        v.sort_unstable();
        let mut j = 0;
        let mut l_ = NULL_LIT; // last literal; [x, x.negate()] means totology.
        let mut result = false;
        for i in 0..v.len() {
            let li = v[i];
            let sat = self.lit2asg(li);
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
            0 => Err(result),
            1 => Err(self.enqueue(v[0], NULL_CLAUSE)),
            _ => Ok(self.inject(learnt, Clause::new(v.to_vec()))),
        }
    }
    pub fn add_clause(&mut self, learnt: bool, v: &mut Vec<Lit>) -> bool {
        match self.clause_new(learnt, v) {
            Err(b) => b,
            Ok(c) => true,
        }
    }
    pub fn lbd_of(&mut self, v: &Vec<Lit>) -> usize {
        let k = 1 + self.lbd_key;
        if 1000_000 < k {
            self.lbd_key = 0;
        }
        let n = v.len();
        let mut cnt = 0;
        for i in 0..n {
            let l = self.vars[v[i].vi()].level;
            let x = self.lbd_seen[l];
            if x != k && l != 0 {
                self.lbd_seen[l] = k;
                cnt += 1;
            }
        }
        max(1, cnt)
    }
    /// renamed from checkRestartCondition
    pub fn should_restart(&mut self, lbd: usize, c_l: usize) -> bool {
        let next = self.next_restart;
        let count = self.get_stat(&StatIndex::NumOfBackjump) as u64;
        let nas = self.num_assigns() as f64;
        let b_l = self.decision_level() as f64;
        let d_f = self.lbd_f.update(lbd as f64);
        let d_s = self.lbd_s.update(lbd as f64);
        let a_f = self.asg_f.update(nas);
        let a_s = self.asg_s.update(nas);
        self.c_lvl.update(c_l as f64);
        let n_b = self.get_stat(&StatIndex::NumOfBlockRestart);
        let n_f = self.get_stat(&StatIndex::NumOfRestart);
        let bias = if 5 < n_b && 5 < n_f {
            0.10 * self.rbias.get()
        } else {
            0.0
        };
        let filled = next <= count;
        let blocking = (1.25 - bias) * a_s < a_f;
        let forcing = (1.25 + bias) * d_s < d_f;
        if !filled {
            self.b_lvl.update(b_l);
            false
        } else {
            self.b_lvl.update(0.0);
            false
        }
    }
}

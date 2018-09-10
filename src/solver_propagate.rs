use clause::ClauseKind;
use clause_manage::ClauseManagement;
use solver::{Solver, Stat};
use solver_analyze::CDCL;
use solver_rollback::Restart;
use std::cmp::max;
use types::*;
use var_manage::VarSelect;
use solver::SatSolver;
use solver::Assignment;

pub const WATCHING: VarId = 2685;

pub trait SolveSAT {
    /// returns `true` for SAT, `false` for UNSAT.
    fn search(&mut self) -> bool;
    fn propagate(&mut self) -> ClauseId;
}

impl SolveSAT for Solver {
    fn propagate(&mut self) -> ClauseId {
        while self.assign.q_head < self.assign.trail.len() {
            let p: usize = self.assign.trail[self.assign.q_head] as usize;
            debug_assert!(1 < p);
            self.check_lit(ClauseKind::Removable, "before propagation", p as Lit);
            self.assign.q_head += 1;
            self.stats[Stat::NumOfPropagation as usize] += 1;
            for cs in &mut self.cp {
                let ret = cs.propagate(&mut self.vars, &mut self.assign, p as Lit);
                if ret != NULL_CLAUSE {
                    return ret;
                }
            }
            // self.check_lit(ClauseKind::Removable, "after propagation", p as Lit);
        }
        NULL_CLAUSE
    }
    fn search(&mut self) -> bool {
        // self.dump("search");
        let root_lv = self.root_level;
        loop {
            // self.dump("calling propagate");
            self.stats[Stat::NumOfPropagation as usize] += 1;
            let ci = self.propagate();
            let d = self.decision_level();
            // self.dump(format!("search called propagate and it returned {:?} at {}", ret, d));
            if ci == NULL_CLAUSE {
                // println!(" search loop enters a new level");
                let na = self.num_assigns();
                if na == self.num_vars {
                    return true;
                }
                self.force_restart();
                if d == 0 && self.num_solved_vars < na {
                    self.simplify_database();
                    self.num_solved_vars = na;
                    self.rebuild_vh();
                }
                if !(self.assign.q_head < self.assign.trail.len()) {
                    let vi = self.select_var();
                    debug_assert_ne!(vi, 0);
                    let p = self.vars[vi].phase;
                    self.assign.uncheck_assume(&mut self.vars[vi], vi.lit(p));
                }
            } else {
                self.stats[Stat::NumOfBackjump as usize] += 1;
                if d == self.root_level {
                    self.analyze_final(ci, false);
                    return false;
                } else {
                    // self.dump(" before analyze");
                    let backtrack_level = self.analyze(ci);
                    self.cancel_until(max(backtrack_level as usize, root_lv));
                    let lbd;
                    if self.an_learnt_lits.len() == 1 {
                        let l = self.an_learnt_lits[0];
                        self.assign.uncheck_enqueue(&mut self.vars[l.vi()], l, NULL_CLAUSE);
                        lbd = 1;
                    } else {
                        let v = self.an_learnt_lits.clone();
                        lbd = self.add_learnt(v);
                    }
                    self.decay_cla_activity();
                    // glucose reduction
                    let conflicts = self.stats[Stat::NumOfBackjump as usize] as usize;
                    if self.cur_restart * self.next_reduction <= conflicts {
                        self.cur_restart =
                            ((conflicts as f64) / (self.next_reduction as f64)) as usize + 1;
                        self.reduce_watchers();
                    }
                    self.block_restart(lbd, d);
                }
                // Since the conflict path pushes a new literal to trail, we don't need to pick up a literal here.
            }
        }
    }
}

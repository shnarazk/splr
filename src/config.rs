use crate::clause::{ClauseDB, ClauseFlag};
use crate::eliminator::Eliminator;
use crate::state::{Stat, State};
use crate::traits::*;
use crate::var::Var;

#[derive(Eq, PartialEq)]
pub enum SearchStrategy {
    Initial,
    Generic,
    LowDecisions,
    HighSuccesive,
    LowSuccesive,
    ManyGlues,
}

impl SearchStrategy {
    pub fn to_str(&self) -> &'static str {
        match self {
            SearchStrategy::Initial => "Initial",
            SearchStrategy::Generic => "Default",
            SearchStrategy::LowDecisions => "LowDecs",
            SearchStrategy::HighSuccesive => "HighSucc",
            SearchStrategy::LowSuccesive => "LowSucc",
            SearchStrategy::ManyGlues => "ManyGlue",
        }
    }
}

/// `Solver`'s parameters; random decision rate was dropped.
pub struct Config {
    pub root_level: usize,
    pub num_vars: usize,
    /// STARATEGY
    pub adapt_strategy: bool,
    pub strategy: SearchStrategy,
    pub use_chan_seok: bool,
    pub co_lbd_bound: usize,
    /// CLAUSE/VARIABLE ACTIVITY
    pub cla_decay: f64,
    pub cla_inc: f64,
    pub var_decay: f64,
    pub var_decay_max: f64,
    pub var_inc: f64,
    /// CLAUSE REDUCTION
    pub first_reduction: usize,
    pub glureduce: bool,
    pub cdb_inc: usize,
    pub cdb_inc_extra: usize,
    pub ema_coeffs: (i32, i32),
    /// RESTART
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glusoce
    pub restart_thr: f64,
    /// For block restart based on average assigments: 1.40.
    /// This is called `R` in Glucose
    pub restart_blk: f64,
    pub restart_asg_len: usize,
    pub restart_lbd_len: usize,
    pub restart_expansion: f64,
    pub restart_step: usize,
    pub luby_restart: bool,
    pub luby_restart_num_conflict: f64,
    pub luby_restart_inc: f64,
    pub luby_current_restarts: usize,
    pub luby_restart_factor: f64,
    /// MISC
    pub use_sve: bool,
    pub progress_log: bool,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            root_level: 0,
            num_vars: 0,
            adapt_strategy: true,
            strategy: SearchStrategy::Initial,
            use_chan_seok: false,
            co_lbd_bound: 5,
            cla_decay: 0.999,
            cla_inc: 1.0,
            var_decay: 0.9,
            var_decay_max: 0.95,
            var_inc: 0.9,
            first_reduction: 1000,
            glureduce: true,
            cdb_inc: 300,
            cdb_inc_extra: 1000,
            restart_thr: 0.75,
            restart_blk: 1.40,
            restart_asg_len: 3500,
            restart_lbd_len: 50,
            restart_expansion: 1.15,
            restart_step: 50,
            luby_restart: false,
            luby_restart_num_conflict: 0.0,
            luby_restart_inc: 2.0,
            luby_current_restarts: 0,
            luby_restart_factor: 100.0,
            ema_coeffs: (2 ^ 5, 2 ^ 15),
            use_sve: true,
            progress_log: false,
        }
    }
}

impl Config {
    #[inline(always)]
    pub fn adapt_strategy(
        &mut self,
        cdb: &mut ClauseDB,
        elim: &mut Eliminator,
        state: &mut State,
        vars: &mut [Var],
    ) {
        if !self.adapt_strategy || self.strategy != SearchStrategy::Initial {
            return;
        }
        let mut re_init = false;
        let decpc = state.stats[Stat::Decision as usize] as f64
            / state.stats[Stat::Conflict as usize] as f64;
        if decpc <= 1.2 {
            self.strategy = SearchStrategy::LowDecisions;
            self.use_chan_seok = true;
            self.co_lbd_bound = 4;
            self.glureduce = true;
            self.first_reduction = 2000;
            state.next_reduction = 2000;
            state.cur_restart = (state.stats[Stat::Conflict as usize] as f64
                / state.next_reduction as f64
                + 1.0) as usize;
            self.cdb_inc = 0;
            re_init = true;
        }
        if state.stats[Stat::NoDecisionConflict as usize] < 30_000 {
            self.strategy = SearchStrategy::LowSuccesive;
            self.luby_restart = true;
            self.luby_restart_factor = 100.0;
            self.var_decay = 0.999;
            self.var_decay_max = 0.999;
        }
        if state.stats[Stat::NoDecisionConflict as usize] > 54_400 {
            self.strategy = SearchStrategy::HighSuccesive;
            self.use_chan_seok = true;
            self.glureduce = true;
            self.co_lbd_bound = 3;
            self.first_reduction = 30000;
            self.var_decay = 0.99;
            self.var_decay_max = 0.99;
            // randomize_on_restarts = 1;
        }
        if state.stats[Stat::NumLBD2 as usize] - state.stats[Stat::NumBin as usize] > 20_000 {
            self.strategy = SearchStrategy::ManyGlues;
            self.var_decay = 0.91;
            self.var_decay_max = 0.91;
        }
        if self.strategy == SearchStrategy::Initial {
            self.strategy = SearchStrategy::Generic;
            return;
        }
        state.ema_asg.reset();
        state.ema_lbd.reset();
        // state.lbd_queue.clear();
        state.stats[Stat::SumLBD as usize] = 0;
        state.stats[Stat::Conflict as usize] = 0;
        if self.use_chan_seok {
            // println!("# Adjusting for low decision levels.");
            // move some clauses with good lbd (col_lbd_bound) to Permanent
            for c in &mut cdb.clause[1..] {
                if c.get_flag(ClauseFlag::Dead) || !c.get_flag(ClauseFlag::Learnt) {
                    continue;
                }
                if c.rank <= self.co_lbd_bound {
                    c.flag_off(ClauseFlag::Learnt);
                    cdb.num_learnt -= 1;
                } else if re_init {
                    c.kill(&mut cdb.touched);
                }
            }
            cdb.garbage_collect(vars, elim);
        }
    }
}

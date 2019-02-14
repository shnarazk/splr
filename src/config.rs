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
    pub lbd_frozen_clause: usize,
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
    pub cdb_soft_limit: usize,
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
    /// Eliminator
    pub use_elim: bool,
    /// 0 for no limit
    /// Stop elimination if a generated resolvent is larger than this
    /// 0 means no limit.
    pub elim_eliminate_combination_limit: usize,
    /// Stop elimination if the increase of clauses is over this
    pub elim_eliminate_grow_limit: usize,
    pub elim_eliminate_loop_limit: usize,
    /// Stop sumsumption if the size of a clause is over this
    pub elim_subsume_literal_limit: usize,
    pub elim_subsume_loop_limit: usize,
    /// MISC
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
            lbd_frozen_clause: 30,
            cla_decay: 0.999,
            cla_inc: 1.0,
            var_decay: 0.9,
            var_decay_max: 0.95,
            var_inc: 0.9,
            first_reduction: 1000,
            glureduce: true,
            cdb_inc: 300,
            cdb_inc_extra: 1000,
            cdb_soft_limit: 18_000_000,
            restart_thr: 0.60,     // will be overwrited by bin/splr
            restart_blk: 1.40,     // will be overwrited by bin/splr
            restart_asg_len: 3500, // will be overwrited by bin/splr
            restart_lbd_len: 100,  // will be overwrited by bin/splr
            restart_expansion: 1.15,
            restart_step: 50,
            luby_restart: false,
            luby_restart_num_conflict: 0.0,
            luby_restart_inc: 2.0,
            luby_current_restarts: 0,
            luby_restart_factor: 100.0,
            ema_coeffs: (2 ^ 5, 2 ^ 15),
            use_elim: true,
            elim_eliminate_combination_limit: 80,
            elim_eliminate_grow_limit: 0, // 64
            elim_eliminate_loop_limit: 2_000_000,
            elim_subsume_literal_limit: 100,
            elim_subsume_loop_limit: 2_000_000,
            progress_log: false,
        }
    }
}

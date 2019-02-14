use std::path::PathBuf;
use structopt::StructOpt;

/// `Solver`'s parameters; random decision rate was dropped.
#[derive(StructOpt, Debug)]
#[structopt(
    name = "splr",
    about = "SAT solver for Propositional Logic in Rust, version 0.1.0"
)]
pub struct ConfigOption {
    /// output filiname; use default rule if it's empty.
    #[structopt(long = "output", short = "o", default_value = "")]
    pub output_filname: String,
    /// a CNF file to solve
    #[structopt(parse(from_os_str))]
    pub cnf: std::path::PathBuf,

    /// Disables dynamic strategy adaptation
    #[structopt(long = "no-adaptation", short = "a")]
    pub no_adapt: bool,
    #[structopt(long = "use_chan_seok")]
    pub use_chan_seok: bool,
    #[structopt(long = "co_lbd_bound", default_value = "5")]
    pub co_lbd_bound: usize,
    #[structopt(long="lbd_frozen_clause", default_value = "30")]
    pub lbd_frozen_clause: usize,
    /// CLAUSE/VARIABLE ACTIVITY
    #[structopt(long = "cla_decay", default_value = "0.999")]
    pub cla_decay: f64,
    #[structopt(long = "cla_inc", default_value = "1.0")]
    pub cla_inc: f64,
    #[structopt(long = "var_decay", default_value = "0.9")]
    pub var_decay: f64,
    #[structopt(long = "var_decay_max", default_value = "0.95")]
    pub var_decay_max: f64,
    #[structopt(long = "var_inc", default_value = "0.9")]
    pub var_inc: f64,
    /// CLAUSE REDUCTION
    #[structopt(long = "first_reduction", default_value = "1000")]
    pub first_reduction: usize,
    #[structopt(long="glureduce")]
    pub glureduce: bool,
    #[structopt(long="cdb_inc", default_value = "300")]
    pub cdb_inc: usize,
    #[structopt(long="cdb_inc_extra", default_value = "1000")]
    pub cdb_inc_extra: usize,
    // clause_limit: usize,
    /// solf limit of clause DB (default is about 4GB)
    #[structopt(long = "cl", default_value = "18000000")]
    pub cdb_soft_limit: usize,
    /// RESTART
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glusoce
    /// threshold for forcing restart (K in Glucose)
    #[structopt(long = "rt", default_value = "0.60")]
    pub restart_thr: f64,
    /// For block restart based on average assigments: 1.40.
    /// This is called `R` in Glucose
    /// threshold for blocking restart (R in Glucose)
    #[structopt(long = "rb", default_value = "1.40")]
    pub restart_blk: f64,
    /// #samples for average assignment rate
    #[structopt(long = "ra", default_value = "3500")]
    pub restart_asg_len: usize,
    /// #samples for average LBD of learnt clauses
    #[structopt(long = "rl", default_value = "50")]
    pub restart_lbd_len: usize,
    #[structopt(long = "restart_expansion", default_value = "1.15")]
    pub restart_expansion: f64,
    /// #conflicts between restarts
    #[structopt(long = "rs", default_value = "50")]
    pub restart_step: usize,
    #[structopt(long = "luby_restart")]
    pub luby_restart: bool,
    #[structopt(long = "luby_restart_num_conflict", default_value = "0.0")]
    pub luby_restart_num_conflict: f64,
    #[structopt(long = "luby_restart_inc", default_value = "2.0")]
    pub luby_restart_inc: f64,
    #[structopt(long = "luby_current_restarts", default_value = "0")]
    pub luby_current_restarts: usize,
    #[structopt(long = "luby_restart_factor", default_value = "100.0")]
    pub luby_restart_factor: f64,
    /// Eliminator
    /// Disables exhaustive simplification
    #[structopt(long = "no-elim", short = "e")]
    pub no_elim: bool,
    /// 0 for no limit
    /// Stop elimination if a generated resolvent is larger than this
    /// 0 means no limit.
    #[structopt(long = "elim_eliminate_combination_limit", default_value = "80")]
    pub elim_eliminate_combination_limit: usize,
    /// Stop elimination if the increase of clauses is over this
    /// grow limit of #clauses by var elimination
    #[structopt(long = "eg", default_value = "0")]
    pub elim_eliminate_grow_limit: usize,
    #[structopt(default_value = "2000000")]
    pub elim_eliminate_loop_limit: usize,
    /// #literals in a merged clause by var elimination
    /// Stop sumsumption if the size of a clause is over this
    #[structopt(long = "el", default_value = "100")]
    pub elim_subsume_literal_limit: usize,
    #[structopt(default_value = "2000000")]
    pub elim_subsume_loop_limit: usize,
    /// MISC
    /// Uses Glucose format for progress report
    #[structopt(long = "--log", short = "l")]
    pub progress_log: bool,
}

impl Default for ConfigOption {
    fn default() -> ConfigOption {
        ConfigOption {
            cnf: PathBuf::new(),
            output_filname: "".to_string(),
            no_adapt: false,
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
            no_elim: false,
            elim_eliminate_combination_limit: 80,
            elim_eliminate_grow_limit: 0, // 64
            elim_eliminate_loop_limit: 2_000_000,
            elim_subsume_literal_limit: 100,
            elim_subsume_loop_limit: 2_000_000,
            progress_log: false,
        }
    }
}


use std::path::PathBuf;
use structopt::StructOpt;

pub const VERSION: &str = "0.1.2+stagnation-013+bi-watchers+conflict-minimization";

/// Configuration built from command line options
#[derive(Clone, Debug, StructOpt)]
#[structopt(
    name = "splr",
    about = "A SAT solver for Propositional Logic in Rust, version 0.1.2+stagnation-013+bi-watchers
https://github.com/shnarazk/splr"
)]
pub struct Config {
    /// soft limit of #clauses (24000000 is about 4GB)
    #[structopt(long = "cl", default_value = "0")]
    pub clause_limit: usize,
    /// grow limit of #clauses by var elimination
    #[structopt(long = "eg", default_value = "4")]
    pub elim_grow_limit: usize,
    /// #literals in a merged clause by var elimination
    #[structopt(long = "el", default_value = "64")]
    pub elim_lit_limit: usize,
    /// #samples for average assignment rate
    #[structopt(long = "ra", default_value = "3500")]
    pub restart_asg_len: usize,
    /// #samples for average LBD of learnt clauses
    #[structopt(long = "rl", default_value = "50")]
    pub restart_lbd_len: usize,
    /// threshold for forcing restart (K in Glucose)
    #[structopt(long = "rt", default_value = "0.60")]
    pub restart_threshold: f64,
    /// threshold for blocking restart (R in Glucose)
    #[structopt(long = "rb", default_value = "1.40")]
    pub restart_blocking: f64,
    /// #conflicts between restarts
    #[structopt(long = "rs", default_value = "50")]
    pub restart_step: usize,
    /// a DIMACS format CNF file
    #[structopt(parse(from_os_str))]
    pub cnf_filename: PathBuf,
    /// output directory, applied to result and proof
    #[structopt(long = "--dir", short = "o", default_value = ".", parse(from_os_str))]
    pub output_dirname: PathBuf,
    /// result filename/stdout; use default if empty
    #[structopt(long = "--result", short = "r", default_value = "", parse(from_os_str))]
    pub result_filename: PathBuf,
    /// filename of DRAT UNSAT certification
    #[structopt(
        long = "proof",
        default_value = "proof.out",
        short = "p",
        parse(from_os_str)
    )]
    pub proof_filename: PathBuf,
    /// Uses Glucose format for progress report
    #[structopt(long = "--log", short = "l")]
    pub use_log: bool,
    /// Disables exhaustive simplification
    #[structopt(long = "no-elim", short = "E")]
    pub no_elim: bool,
    /// Disables dynamic restart adaptation
    #[structopt(long = "no-adaptive_restart", short = "R")]
    pub no_adaptive_restart: bool,
    /// Disables dynamic strategy adaptation
    #[structopt(long = "no-adaptive_strategy", short = "S")]
    pub no_adaptive_strategy: bool,
    /// Disables pendulum search model
    #[structopt(long = "no-pendulum", short = "P")]
    pub no_stagnation: bool,
    /// Disables learnt minimization
    #[structopt(long = "learnt-min", short = "M")]
    pub learnt_minimization: bool,
    /// Writes a DRAT UNSAT certification file
    #[structopt(long = "certify", short = "c")]
    pub use_certification: bool,
    /// CPU time limit in sec. (zero for no limit)
    #[structopt(long = "to", default_value = "0")]
    pub timeout: f64,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            clause_limit: 18_000_000,
            elim_grow_limit: 0,
            elim_lit_limit: 100,
            restart_asg_len: 3500,
            restart_lbd_len: 50,
            restart_threshold: 0.60,
            restart_blocking: 1.40,
            restart_step: 50,
            cnf_filename: PathBuf::new(),
            output_dirname: PathBuf::from("."),
            result_filename: PathBuf::new(),
            proof_filename: PathBuf::from("proof.out"),
            use_log: false,
            no_elim: false,
            no_adaptive_restart: false,
            no_adaptive_strategy: false,
            no_stagnation: false,
            learnt_minimization: false,
            use_certification: false,
            timeout: 0.0,
        }
    }
}

impl<T> From<T> for Config
where
    PathBuf: From<T>,
{
    fn from(path: T) -> Config {
        let mut config = Config::default();
        config.cnf_filename = PathBuf::from(path);
        config
    }
}

/// Crate `config` provides solver's configuration and CLI.
use {crate::types::DecisionLevel, std::path::PathBuf, structopt::StructOpt};

/// Splr version number.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Configuration built from command line options
#[derive(Clone, Debug, StructOpt)]
#[structopt(name = "splr", about, author)]
pub struct Config {
    // ////////////////////////////////////////////////////////////////////////////////
    // I/O configuration
    //

    /// a DIMACS format CNF file
    #[structopt(parse(from_os_str))]
    pub cnf_filename: PathBuf,

    /// interval for dumpping stat data
    #[structopt(long = "stat", default_value = "0")]
    pub dump_interval: usize,

    /// output directory
    #[structopt(long = "dir", short = "o", default_value = ".", parse(from_os_str))]
    pub output_dirname: PathBuf,

    /// filename for DRAT cert.
    #[structopt(
        long = "proof",
        default_value = "proof.out",
        short = "p",
        parse(from_os_str)
    )]
    pub proof_filename: PathBuf,

    /// Disable any progress message
    #[structopt(long = "quiet", short = "q")]
    pub quiet_mode: bool,

    /// result filename/stdout
    #[structopt(long = "result", short = "r", default_value = "", parse(from_os_str))]
    pub result_filename: PathBuf,

    /// Uses Glucose-like progress report
    #[structopt(long = "log", short = "l")]
    pub use_log: bool,

    // ////////////////////////////////////////////////////////////////////////////////
    // clause DB
    //

    /// soft limit of #clauses (6MC/GB)
    #[structopt(long = "cl", default_value = "0")]
    pub clause_limit: usize,

    /// disable clause reduction
    #[structopt(long = "without-reduce")]
    pub without_reduce: bool,

    //
    // eliminator
    //
    /// grow limit of #clauses by v-elim
    #[structopt(long = "eg", default_value = "0")]
    pub elim_grow_limit: usize,

    /// #literals in a clause by v-elim
    #[structopt(long = "el", default_value = "100")]
    pub elim_lit_limit: usize,

    /// Disables exhaustive simplification
    #[structopt(long = "without-elim", short = "E")]
    pub without_elim: bool,

    // ////////////////////////////////////////////////////////////////////////////////
    // restarter
    //

    /// length for assignment average
    #[structopt(long = "ra", default_value = "3500")]
    pub restart_asg_len: usize,

    /// blocking restart threshold
    #[structopt(long = "rb", default_value = "1.40")]
    pub restart_blocking: f64, // Glucose's R

    /// length for LBD average
    #[structopt(long = "rl", default_value = "50")]
    pub restart_lbd_len: usize,

    /// #conflicts between restarts
    #[structopt(long = "rs", default_value = "50")]
    pub restart_step: usize,

    /// forcing restart threshold
    #[structopt(long = "rt", default_value = "0.70")]
    pub restart_threshold: f64, // Glucose's K

    // ////////////////////////////////////////////////////////////////////////////////
    // solver configuration
    //

    /// threshold to use chronoBT
    #[structopt(long = "chronoBT", short = "C", default_value = "100")]
    pub chronobt: DecisionLevel,

    /// CPU time limit in sec.
    #[structopt(long = "to", default_value = "10000.0")]
    pub timeout: f64,

    /// Writes a DRAT UNSAT certification file
    #[structopt(long = "certify", short = "c")]
    pub use_certification: bool,

    /// Disables dynamic strategy adaptation
    #[structopt(long = "no-adaptive-strategy", short = "S")]
    pub without_adaptive_strategy: bool,

    /// Enables deep search mode
    #[structopt(skip)]
    pub with_deep_search: bool,

}

impl Default for Config {
    fn default() -> Config {
        Config {
            // I/O
            cnf_filename: PathBuf::new(),
            dump_interval: 0,
            output_dirname: PathBuf::from("."),
            proof_filename: PathBuf::from("proof.out"),
            quiet_mode: false,
            result_filename: PathBuf::new(),
            use_log: false,

            // clause DB
            clause_limit: 0,
            without_reduce: false,

            // eliminator
            elim_grow_limit: 0,
            elim_lit_limit: 100,
            without_elim: false,

            // restarter
            restart_asg_len: 3500,
            restart_blocking: 1.40,
            restart_lbd_len: 50,
            restart_step: 50,
            restart_threshold: 0.60,

            // solver
            chronobt: 100,
            timeout: 10_000.0,
            use_certification: false,
            without_adaptive_strategy: false,
            with_deep_search: false,
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

impl Config {
    pub fn override_args(mut self) -> Config {
        self.without_reduce = true;
        self
    }
}

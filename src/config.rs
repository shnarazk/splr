use std::path::PathBuf;
use structopt::StructOpt;

pub const VERSION: &str = "0.2.0-RC0";

pub const EMA_FAST: usize = 64; // 2 ^ 6
pub const EMA_SLOW: usize = 32768; // 2 ^ 15

pub const RESTART_INTV: usize = EMA_FAST / 2;
pub const RESTART_QNTM: usize = 10_000;
pub const RESTART_THRD: (f64, f64) = (0.4, 0.9);

pub const ACR_THRESHOLD: f64 = 1.4;
// pub const AVS_THRESHOLD: f64 = 1.25;

/// Configuration built from command line options
#[derive(Clone, Debug, StructOpt)]
#[structopt(name = "splr", about, author)]
pub struct Config {
    /// soft limit of #clauses (24M~4GB)
    #[structopt(long = "cl", default_value = "0")]
    pub clause_limit: usize,
    /// scaling for A. Clause Refinement
    #[structopt(long = "rc", default_value = "1.6")]
    pub restart_acr: f64,
    /// scaling for A. Var. Segmentation
    #[structopt(long = "rv", default_value = "1.6")]
    pub restart_avs: f64,
    // /// minimal interval of restarts
    // #[structopt(long = "ri", default_value = "32")]
    // pub restart_interval: usize,
    // /// steps of fup quantization
    // #[structopt(long = "rq", default_value = "1024")]
    // pub restart_quantum: usize,
    /// grow limit of #clauses by v-elim.
    #[structopt(long = "eg", default_value = "4")]
    pub elim_grow_limit: usize,
    /// #literals in a clause in v-elim.
    #[structopt(long = "el", default_value = "64")]
    pub elim_lit_limit: usize,
    /// init. var. activity decay
    #[structopt(long = "vd", default_value = "0.90")]
    pub var_activity_decay: f64,
    /// max. var. activity decay
    #[structopt(long = "vm", default_value = "0.96")]
    pub var_activity_d_max: f64,
    /// a DIMACS format CNF file
    #[structopt(parse(from_os_str))]
    pub cnf_filename: PathBuf,
    /// output directory
    #[structopt(long = "--dir", short = "o", default_value = ".", parse(from_os_str))]
    pub output_dirname: PathBuf,
    /// result filename or stdout
    #[structopt(long = "--result", short = "r", default_value = "", parse(from_os_str))]
    pub result_filename: PathBuf,
    /// filename for DRAT cert.
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
    /// Disables exhaustive clause/var elimination
    #[structopt(long = "no-elim", short = "E")]
    pub without_elim: bool,
    /// Disables dynamic strategy adaptation
    #[structopt(long = "no-adaptive_strategy", short = "S")]
    pub without_adaptive_strategy: bool,
    /// Writes a DRAT UNSAT certification
    #[structopt(long = "certify", short = "c")]
    pub use_certification: bool,
    /// soft limit for CPU time in sec.
    #[structopt(long = "to", default_value = "0")]
    pub timeout: f64,
    /// Interval for dumping stat info.
    #[structopt(long = "stat", default_value = "0")]
    pub dump_interval: usize,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            clause_limit: 18_000_000,
            restart_acr: ACR_THRESHOLD,
            restart_avs: 0.99,
            // restart_interval: RESTART_INTV,
            // restart_quantum: RESTART_QNTM,
            elim_grow_limit: 4,
            elim_lit_limit: 100,
            var_activity_decay: 0.90,
            var_activity_d_max: 0.98,
            cnf_filename: PathBuf::new(),
            output_dirname: PathBuf::from("."),
            result_filename: PathBuf::new(),
            proof_filename: PathBuf::from("proof.out"),
            use_log: false,
            without_elim: false,
            without_adaptive_strategy: false,
            use_certification: false,
            timeout: 0.0,
            dump_interval: 0,
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

/// Crate `config` provides solver's configuration and CLI.
use {crate::types::DecisionLevel, std::path::PathBuf, structopt::StructOpt};

/// Splr version number.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Configuration built from command line options
#[derive(Clone, Debug, StructOpt)]
#[structopt(name = "splr", about, author)]
pub struct Config {
    //
    //## I/O configuration
    //
    /// CNF file in DIMACS format
    #[structopt(parse(from_os_str))]
    pub cnf_file: PathBuf,

    /// Interval for dumpping stat data
    #[structopt(long = "stat", default_value = "0")]
    pub dump_int: usize,

    /// Disable coloring
    #[structopt(long = "no-color", short = "C")]
    pub no_color: bool,

    /// Output directory
    #[structopt(long = "dir", short = "o", default_value = ".", parse(from_os_str))]
    pub output_dir: PathBuf,

    /// Cert. file in DRAT format
    #[structopt(
        long = "proof",
        default_value = "proof.out",
        short = "p",
        parse(from_os_str)
    )]
    pub proof_file: PathBuf,

    /// Disable any progress message
    #[structopt(long = "quiet", short = "q")]
    pub quiet_mode: bool,

    /// Result filename/stdout
    #[structopt(long = "result", short = "r", default_value = "", parse(from_os_str))]
    pub result_file: PathBuf,

    /// Uses Glucose-like progress report
    #[structopt(long = "log", short = "l")]
    pub use_log: bool,

    //
    //## clause DB
    //
    /// Soft limit of #clauses (6MC/GB)
    #[structopt(long = "cl", default_value = "0")]
    pub clause_limit: usize,

    /// Disable clause reduction
    #[structopt(long = "no-reduce", short = "R")]
    pub without_reduce: bool,

    //
    //## eliminator
    //
    /// Grow limit of #clauses by v-elim
    #[structopt(long = "eg", default_value = "0")]
    pub elim_grw_lim: usize,

    /// #literals in a clause by v-elim
    #[structopt(long = "el", default_value = "100")]
    pub elim_lit_lim: usize,

    /// Threshold to elimination
    #[structopt(long = "et", default_value = "128")]
    pub elim_trigger: usize,

    /// Disables exhaustive simplification
    #[structopt(long = "no-elim", short = "E")]
    pub without_elim: bool,

    //
    //## restarter
    //
    /// Enable Bucket restart
    #[structopt(long = "bucket-restart", short = "B")]
    pub bucket_restart: bool,

    /// #conflicts between restarts
    #[structopt(long = "rs", default_value = "50")]
    pub rst_step: usize,

    /// Bucket increment step
    #[structopt(long = "rbi", default_value = "1.0")]
    pub rst_bkt_inc: f64,

    /// Bucket power factor
    #[structopt(long = "rbp", default_value = "1.5")]
    pub rst_bkt_pwr: f64,

    /// Bucket time scale
    #[structopt(long = "rbs", default_value = "0.001")]
    pub rst_bkt_scl: f64,

    /// Bucket threshold
    #[structopt(long = "rbt", default_value = "2000.0")]
    pub rst_bkt_thr: f64,

    /// Length for assignment average
    #[structopt(long = "ral", default_value = "3500")]
    pub rst_asg_len: usize,

    /// Blocking restart threshold
    #[structopt(long = "rab", default_value = "1.40")]
    pub rst_asg_thr: f64, // Glucose's R

    /// Short Length for LBD average
    #[structopt(long = "rll", default_value = "50")]
    pub rst_lbd_len: usize,

    /// Long Length for LBD average
    #[structopt(long = "rll", default_value = "10000")]
    pub rst_lbd_lng: usize,

    /// Forcing restart threshold
    #[structopt(long = "rlt", default_value = "1.1")]
    pub rst_lbd_thr: f64, // Glucose's K

    /// Stabilizer scaling
    #[structopt(long = "rss", default_value = "2.0")]
    pub rst_stb_scl: f64,

    /// Disable geometric restart blocker
    #[structopt(long = "no-stabilizer", short = "S")]
    pub without_stab: bool,

    //
    //## solver configuration
    //
    /// Level threshold to use chronoBT
    #[structopt(long = "cbt", default_value = "100")]
    pub cbt_thr: DecisionLevel,

    /// Disables dynamic strategy adaptation
    #[structopt(long = "no-adapt", short = "A")]
    pub without_adaptive_strategy: bool,

    /// CPU time limit in sec.
    #[structopt(long = "timeout", short = "t", default_value = "10000.0")]
    pub timeout: f64,

    /// Writes a DRAT UNSAT certification file
    #[structopt(long = "certify", short = "c")]
    pub use_certification: bool,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            // I/O
            cnf_file: PathBuf::new(),
            dump_int: 0,
            no_color: false,
            output_dir: PathBuf::from("."),
            proof_file: PathBuf::from("proof.out"),
            quiet_mode: false,
            result_file: PathBuf::new(),
            use_log: false,

            // clause DB
            clause_limit: 0,
            without_reduce: false,

            // eliminator
            elim_grw_lim: 0,
            elim_lit_lim: 100,
            elim_trigger: 128,
            without_elim: false,

            // restarter
            bucket_restart: false,
            rst_step: 50,
            rst_bkt_inc: 1.0,
            rst_bkt_pwr: 1.5,
            rst_bkt_scl: 0.001,
            rst_bkt_thr: 2000.0,
            rst_asg_len: 3500,
            rst_asg_thr: 1.40,
            rst_lbd_len: 50,
            rst_lbd_lng: 10000,
            rst_lbd_thr: 1.2,
            rst_stb_scl: 2.0,
            without_stab: false,

            // solver
            cbt_thr: 100,
            timeout: 10_000.0,
            use_certification: false,
            without_adaptive_strategy: false,
        }
    }
}

impl<T> From<T> for Config
where
    PathBuf: From<T>,
{
    fn from(path: T) -> Config {
        let mut config = Config::default();
        config.cnf_file = PathBuf::from(path);
        config
    }
}

impl Config {
    #[allow(unused_mut)]
    pub fn override_args(mut self) -> Config {
        self.bucket_restart = true;
        self.rst_bkt_pwr = 1.5;
        self
    }
}

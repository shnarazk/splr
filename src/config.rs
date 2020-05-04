/// Crate `config` provides solver's configuration and CLI.
use {crate::types::DecisionLevel, std::path::PathBuf, structopt::StructOpt};

/// Configuration built from command line options
#[derive(Clone, Debug, Default, StructOpt)]
#[structopt(name = "splr", about, author)]
pub struct Config {
    //
    //## I/O configuration
    //
    /// CNF file in DIMACS format
    #[structopt(parse(from_os_str))]
    pub cnf_file: PathBuf,

    /// Interval for dumping stat data
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

    /// Clause reduction switch
    #[structopt(long = "RDC", default_value = "1")]
    reduce: i32,

    //
    //## eliminator
    //
    /// Max #lit for clause subsume
    #[structopt(long = "ecl", default_value = "100")]
    pub elim_cls_lim: usize,

    /// Max #cls for var elimination
    #[structopt(long = "evo", default_value = "10000")]
    pub elim_var_occ: usize,

    /// Grow limit of #cls in var elim.
    #[structopt(long = "evl", default_value = "0")]
    pub elim_grw_lim: usize,

    /// #cls to start simplification
    #[structopt(long = "et", default_value = "40000")]
    pub elim_trigger: usize,

    /// Pre/in-processor switch
    #[structopt(long = "PRO", default_value = "1")]
    elim: i32,

    //
    //## restarter
    //
    /// #conflicts between restarts
    #[structopt(long = "rs", default_value = "50")]
    pub rst_step: usize,

    /// Bucket increment step
    #[structopt(skip)] // long = "rbi", default_value = "1.0"
    pub rst_bkt_inc: f64,

    /// Bucket power factor
    #[structopt(skip)] // long = "rbp", default_value = "1.5"
    pub rst_bkt_pwr: f64,

    /// Bucket time scale
    #[structopt(skip)] // long = "rbs", default_value = "0.001"
    pub rst_bkt_scl: f64,

    /// Bucket threshold
    #[structopt(skip)] // long = "rbt", default_value = "2000"
    pub rst_bkt_thr: usize,

    /// Length for assignment average
    #[structopt(long = "ral", default_value = "3500")]
    pub rst_asg_len: usize,

    /// Blocking restart threshold
    #[structopt(long = "rab", default_value = "1.40")]
    pub rst_asg_thr: f64, // Glucose's R

    /// Length of LBD fast EMA
    #[structopt(long = "rll", default_value = "50")]
    pub rst_lbd_len: usize,

    /// Length of LBD slow EMA
    #[structopt(long = "rls", default_value = "10000")]
    pub rst_lbd_slw: usize,

    /// Forcing restart threshold
    #[structopt(long = "rlt", default_value = "0.70")]
    pub rst_lbd_thr: f64, // Glucose's K

    /// Stabilizer scaling
    #[structopt(long = "rss", default_value = "2.0")]
    pub rst_stb_scl: f64,

    //
    //## solver configuration
    //
    /// Level threshold to use chronoBT
    #[structopt(long = "cbt", default_value = "100")]
    pub cbt_thr: DecisionLevel,

    /// Reason-Side Rewarding switch
    #[structopt(long = "RSR", default_value = "1")]
    rsr: i32,

    /// Stabilization switch
    #[structopt(long = "STB", default_value = "1")]
    stabilize: i32,

    /// Strategy adaptation switch
    #[structopt(long = "ADP", default_value = "1")]
    adaptive: i32,

    /// CPU time limit in sec.
    #[structopt(long = "timeout", short = "t", default_value = "5000.0")]
    pub timeout: f64,

    /// Writes a DRAT UNSAT certification file
    #[structopt(long = "certify", short = "c")]
    pub use_certification: bool,
}

impl<T> From<T> for Config
where
    PathBuf: From<T>,
{
    fn from(path: T) -> Config {
        let f = PathBuf::from(path).into_os_string();
        Config::from_iter([std::ffi::OsString::from("splr"), f].iter())
    }
}

macro_rules! dispatch {
    ($field: expr) => {
        0 < $field
    };
    ($field: expr, $default: expr) => {
        match $field {
            0 => $default,
            x => 0 < x,
        }
    };
}

impl Config {
    #[allow(unused_mut)]
    pub fn override_args(mut self) -> Config {
        // self.without_adaptive_strategy = true;
        // self.stabilize = true;
        self
    }
    pub fn use_reduce(&self) -> bool {
        dispatch!(self.reduce)
    }
    pub fn use_elim(&self) -> bool {
        dispatch!(self.elim)
    }
    pub fn use_reason_side_rewarding(&self) -> bool {
        dispatch!(self.rsr)
    }

    pub fn use_stabilize(&self) -> bool {
        dispatch!(self.stabilize)
    }
    pub fn use_adaptive(&self) -> bool {
        dispatch!(self.adaptive)
    }
}

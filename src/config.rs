#[cfg(not(feature = "no_IO"))]
use structopt::StructOpt;
/// Crate `config` provides solver's configuration and CLI.
use {crate::types::DecisionLevel, std::path::PathBuf};

/// Configuration built from command line options
#[derive(Clone, Debug)]
#[cfg_attr(not(feature = "no_IO"), derive(StructOpt))]
#[cfg_attr(not(feature = "no_IO"), structopt(name = "splra", about, author))]
pub struct Config {
    //
    //## I/O configuration
    //
    /// CNF file in DIMACS format
    #[cfg_attr(not(feature = "no_IO"), structopt(parse(from_os_str)))]
    pub cnf_file: PathBuf,

    /// Interval for dumping stat data
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "stat", default_value = "0"))]
    pub dump_int: usize,

    /// Disable coloring
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "no-color", short = "C"))]
    pub no_color: bool,

    /// Output directory
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "dir", short = "o", default_value = ".", parse(from_os_str))
    )]
    pub output_dir: PathBuf,

    /// Cert. file in DRAT format
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(
            long = "proof",
            default_value = "proof.out",
            short = "p",
            parse(from_os_str)
        )
    )]
    pub proof_file: PathBuf,

    /// Disable any progress message
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "quiet", short = "q"))]
    pub quiet_mode: bool,

    /// Result filename/stdout
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "result", short = "r", default_value = "", parse(from_os_str))
    )]
    pub result_file: PathBuf,

    /// Uses Glucose-like progress report
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "log", short = "l"))]
    pub use_log: bool,

    //
    //## clause DB
    //
    /// Soft limit of #clauses (6MC/GB)
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "cl", default_value = "0"))]
    pub clause_limit: usize,

    /// Clause reduction switch
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "RDC", default_value = "1"))]
    reduce: i32,

    //
    //## eliminator
    //
    /// Max #lit for clause subsume
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "ecl", default_value = "100"))]
    pub elim_cls_lim: usize,

    /// Max #cls for var elimination
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "evo", default_value = "10000")
    )]
    pub elim_var_occ: usize,

    /// Grow limit of #cls in var elim.
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "evl", default_value = "0"))]
    pub elim_grw_lim: usize,

    /// #cls to start simplification
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "et", default_value = "40000")
    )]
    pub elim_trigger: usize,

    /// Pre/in-processor switch
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "PRO", default_value = "1"))]
    elim: i32,

    //
    //## restarter
    //
    /// #conflicts between restarts
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "rs", default_value = "50"))]
    pub rst_step: usize,

    /// Bucket increment step
    #[cfg_attr(not(feature = "no_IO"), structopt(skip))] // long = "rbi", default_value = "1.0"
    pub rst_bkt_inc: f64,

    /// Bucket power factor
    #[cfg_attr(not(feature = "no_IO"), structopt(skip))] // long = "rbp", default_value = "1.5"
    pub rst_bkt_pwr: f64,

    /// Bucket time scale
    #[cfg_attr(not(feature = "no_IO"), structopt(skip))]
    // long = "rbs", default_value = "0.001"
    pub rst_bkt_scl: f64,

    /// Bucket threshold
    #[cfg_attr(not(feature = "no_IO"), structopt(skip))]
    // long = "rbt", default_value = "2000"
    pub rst_bkt_thr: usize,

    /// Length for assignment average
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "ral", default_value = "3500")
    )]
    pub rst_asg_len: usize,

    /// Blocking restart threshold
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "rab", default_value = "1.40")
    )]
    pub rst_asg_thr: f64, // Glucose's R

    /// Length of LBD fast EMA
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "rll", default_value = "50"))]
    pub rst_lbd_len: usize,

    /// Length of LBD slow EMA
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "rls", default_value = "10000")
    )]
    pub rst_lbd_slw: usize,

    /// Forcing restart threshold
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "rlt", default_value = "0.70")
    )]
    pub rst_lbd_thr: f64, // Glucose's K

    /// Stabilizer scaling
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "rss", default_value = "2.0"))]
    pub rst_stb_scl: f64,

    //
    //## var rewarding
    //
    /// Initial var reward decay
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "vri", default_value = "0.75")
    )]
    pub vrw_dcy_beg: f64,

    /// Maximum var reward decay
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "vrm", default_value = "0.98")
    )]
    pub vrw_dcy_end: f64,

    //
    //## solver configuration
    //
    /// Level threshold to use chronoBT
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "cbt", default_value = "100"))]
    pub cbt_thr: DecisionLevel,

    /// Rephase switch
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "RPH", default_value = "1"))]
    rephase: i32,

    /// Reason-Side Rewarding switch
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "RSR", default_value = "1"))]
    rsr: i32,

    /// Stabilization switch
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "STB", default_value = "0"))]
    stabilize: i32,

    /// Strategy adaptation switch
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "ADP", default_value = "1"))]
    adaptive: i32,

    /// CPU time limit in sec.
    #[cfg_attr(
        not(feature = "no_IO"),
        structopt(long = "timeout", short = "t", default_value = "5000.0")
    )]
    pub timeout: f64,

    /// Writes a DRAT UNSAT certification file
    #[cfg_attr(not(feature = "no_IO"), structopt(long = "certify", short = "c"))]
    pub use_certification: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            cnf_file: PathBuf::new(),
            dump_int: 0,
            no_color: true,
            output_dir: PathBuf::new(),
            proof_file: PathBuf::new(),
            quiet_mode: true,
            result_file: PathBuf::new(),
            use_log: false,
            clause_limit: 0,
            reduce: 1,
            elim_cls_lim: 100,
            elim_var_occ: 10_000,
            elim_grw_lim: 0,
            elim_trigger: 40000,
            elim: 1,
            rst_step: 50,
            rst_bkt_inc: 1.0,
            rst_bkt_pwr: 1.5,
            rst_bkt_scl: 0.001,
            rst_bkt_thr: 2000,
            rst_asg_len: 3500,
            rst_asg_thr: 1.4,
            rst_lbd_len: 50,
            rst_lbd_slw: 10000,
            rst_lbd_thr: 0.7,
            rst_stb_scl: 2.0,
            vrw_dcy_beg: 0.10,
            vrw_dcy_end: 0.97,
            cbt_thr: 100,
            rephase: 1,
            rsr: 1,
            stabilize: 1,
            adaptive: 1,
            timeout: 5000.0,
            use_certification: false,
        }
    }
}

impl<T> From<T> for Config
where
    PathBuf: From<T>,
{
    #[cfg(feature = "no_IO")]
    fn from(path: T) -> Config {
        Config {
            cnf_file: PathBuf::from(path),
            ..Config::default()
        }
    }
    #[cfg(not(feature = "no_IO"))]
    fn from(path: T) -> Config {
        let f = PathBuf::from(path).into_os_string();
        Config::from_iter([std::ffi::OsString::from("splr"), f].iter())
    }
}

macro_rules! dispatch {
    // from `0` and `1`
    ($field: expr) => {
        0 != $field
    };
    // from -1, 0, 1
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
        self
    }
    pub fn use_reduce(&self) -> bool {
        dispatch!(self.reduce)
    }
    pub fn use_elim(&self) -> bool {
        dispatch!(self.elim)
    }
    pub fn use_rephase(&self) -> bool {
        dispatch!(self.rephase)
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

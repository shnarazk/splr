/// Crate `config_no_io` provides solver's configuration without CLI.
use {crate::types::DecisionLevel, std::path::PathBuf};

/// Configuration built from command line options
#[derive(Clone, Debug)]
pub struct Config {
    //
    //## I/O configuration
    //
    /// CNF file in DIMACS format
    pub cnf_file: PathBuf,

    /// Interval for dumping stat data
    pub dump_int: usize,

    /// Disable coloring
    pub no_color: bool,

    /// Output directory
    pub output_dir: PathBuf,

    /// Cert. file in DRAT format
    pub proof_file: PathBuf,

    /// Disable any progress message
    pub quiet_mode: bool,

    /// Result filename/stdout
    pub result_file: PathBuf,

    /// Uses Glucose-like progress report
    pub use_log: bool,

    //
    //## clause DB
    //
    /// Soft limit of #clauses (6MC/GB)
    pub clause_limit: usize,

    /// Clause reduction switch
    reduce: i32,

    //
    //## eliminator
    //
    /// Max #lit for clause subsume
    pub elim_cls_lim: usize,

    /// Max #cls for var elimination
    pub elim_var_occ: usize,

    /// Grow limit of #cls in var elim.
    pub elim_grw_lim: usize,

    /// #cls to start simplification
    pub elim_trigger: usize,

    /// Pre/in-processor switch
    elim: i32,

    //
    //## restarter
    //
    /// #conflicts between restarts
    pub rst_step: usize,

    /// Bucket increment step
    pub rst_bkt_inc: f64,

    /// Bucket power factor
    pub rst_bkt_pwr: f64,

    /// Bucket time scale
    pub rst_bkt_scl: f64,

    /// Bucket threshold
    pub rst_bkt_thr: usize,

    /// Length for assignment average
    pub rst_asg_len: usize,

    /// Blocking restart threshold
    pub rst_asg_thr: f64, // Glucose's R

    /// Length of LBD fast EMA
    pub rst_lbd_len: usize,

    /// Length of LBD slow EMA
    pub rst_lbd_slw: usize,

    /// Forcing restart threshold
    pub rst_lbd_thr: f64, // Glucose's K

    /// Stabilizer scaling
    pub rst_stb_scl: f64,

    //
    //## var rewarding
    //
    /// Initial var reward decay
    #[structopt(long = "vri", default_value = "0.10")]
    pub vrw_dcy_beg: f64,

    /// Maximum var reward decay
    #[structopt(long = "vrm", default_value = "0.97")]
    pub vrw_dcy_end: f64,

    //
    //## solver configuration
    //
    /// Level threshold to use chronoBT
    pub cbt_thr: DecisionLevel,

    /// Rephase switch
    rephase: i32,

    /// Reason-Side Rewarding switch
    rsr: i32,

    /// Stabilization switch
    stabilize: i32,

    /// Strategy adaptation switch
    adaptive: i32,

    /// CPU time limit in sec.
    pub timeout: f64,

    /// Writes a DRAT UNSAT certification file
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
    fn from(_: T) -> Config {
        Config::default()
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

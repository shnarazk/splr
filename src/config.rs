#[cfg(feature = "structopt")]
use structopt::StructOpt;
/// Crate `config` provides solver's configuration and CLI.
use {crate::types::DecisionLevel, std::path::PathBuf};

/// Configuration built from command line options
#[derive(Clone, Debug)]
#[cfg_attr(feature = "structopt", derive(StructOpt))]
#[cfg_attr(feature = "structopt", structopt(name = "splr", about, author))]
pub struct Config {
    //
    // Switches
    //
    /// Strategy adaptation switch      .
    #[cfg_attr(feature = "structopt", structopt(long = "ADP", default_value = "1"))]
    a_adaptive: i32,

    /// Eliminator switch               .
    #[cfg_attr(feature = "structopt", structopt(long = "ELI", default_value = "1"))]
    a_elim: i32,

    /// Rephase switch                  .
    #[cfg_attr(feature = "structopt", structopt(long = "RPH", default_value = "1"))]
    a_rephase: i32,

    /// Reason-Side Rewarding switch    .
    #[cfg_attr(feature = "structopt", structopt(long = "RSR", default_value = "1"))]
    a_rsr: i32,

    /// Stabilization switch            .
    #[cfg_attr(feature = "structopt", structopt(long = "STB", default_value = "1"))]
    a_stabilize: i32,

    /// Clause reduction switch         .
    #[cfg_attr(feature = "structopt", structopt(long = "RDC", default_value = "1"))]
    a_reduce: i32,

    /// Vivification switch             .
    #[cfg_attr(feature = "structopt", structopt(long = "VIV", default_value = "1"))]
    a_vivify: i32,

    //
    //## solver configuration
    //
    /// Dec. lvl to use chronoBT      .
    #[cfg_attr(feature = "structopt", structopt(long = "cbt", default_value = "100"))]
    pub c_cbt_thr: DecisionLevel,

    /// Soft limit of #clauses (6MC/GB) .
    #[cfg_attr(feature = "structopt", structopt(long = "cl", default_value = "0"))]
    pub c_cls_lim: usize,

    /// #cls to start in-processor  .
    #[cfg_attr(feature = "structopt", structopt(long = "ii", default_value = "25000"))]
    pub c_ip_int: usize,

    /// CPU time limit in sec.     .
    #[cfg_attr(
        feature = "structopt",
        structopt(long = "timeout", short = "t", default_value = "5000.0")
    )]
    pub c_tout: f64,

    //
    //## I/O configuration
    //
    /// Build Splr interface            .
    #[cfg_attr(feature = "structopt", structopt(skip))]
    pub splr_interface: bool,

    /// DIMACS CNF file                 .
    #[cfg_attr(feature = "structopt", structopt(parse(from_os_str)))]
    pub cnf_file: PathBuf,

    /// Interval for dumping stat data  .
    #[cfg_attr(feature = "structopt", structopt(long = "stat", default_value = "0"))]
    pub io_dump: usize,

    /// Output directory                .
    #[cfg_attr(
        feature = "structopt",
        structopt(long = "dir", short = "o", default_value = ".", parse(from_os_str))
    )]
    pub io_odir: PathBuf,

    /// DRAT Cert. filename     .
    #[cfg_attr(
        feature = "structopt",
        structopt(
            long = "proof",
            default_value = "proof.out",
            short = "p",
            parse(from_os_str)
        )
    )]
    pub io_pfile: PathBuf,

    /// Result filename/stdout           .
    #[cfg_attr(
        feature = "structopt",
        structopt(long = "result", short = "r", default_value = "", parse(from_os_str))
    )]
    pub io_rfile: PathBuf,

    /// Disable coloring
    #[cfg_attr(feature = "structopt", structopt(long = "no-color", short = "C"))]
    pub no_color: bool,

    /// Disable any progress message
    #[cfg_attr(feature = "structopt", structopt(long = "quiet", short = "q"))]
    pub quiet_mode: bool,

    /// Writes a DRAT UNSAT certification file
    #[cfg_attr(feature = "structopt", structopt(long = "certify", short = "c"))]
    pub use_certification: bool,

    /// Uses Glucose-like progress report
    #[cfg_attr(feature = "structopt", structopt(long = "log", short = "l"))]
    pub use_log: bool,

    //
    //## eliminator
    //
    /// Max #lit for clause subsume    .
    #[cfg_attr(feature = "structopt", structopt(long = "ecl", default_value = "32"))]
    pub elim_cls_lim: usize,

    /// Grow limit of #cls in var elim. .
    #[cfg_attr(feature = "structopt", structopt(long = "evl", default_value = "0"))]
    pub elim_grw_lim: usize,

    /// Max #cls for var elimination .
    #[cfg_attr(feature = "structopt", structopt(long = "evo", default_value = "8192"))]
    pub elim_var_occ: usize,

    //
    //## restarter
    //
    /// #conflicts between restarts    .
    #[cfg_attr(feature = "structopt", structopt(long = "rs", default_value = "50"))]
    pub rst_step: usize,

    /// Length of assign. fast EMA     .
    #[cfg_attr(feature = "structopt", structopt(long = "ral", default_value = "50"))]
    pub rst_asg_len: usize,

    /// Length of assign. slow EMA  .
    #[cfg_attr(
        feature = "structopt",
        structopt(long = "ras", default_value = "10000")
    )]
    pub rst_asg_slw: usize,

    /// Blocking restart threshold    .
    #[cfg_attr(feature = "structopt", structopt(long = "rat", default_value = "1.4"))]
    pub rst_asg_thr: f64, // Glucose's R

    /// Conflict Correlation threshold
    #[cfg_attr(feature = "structopt", structopt(long = "rct", default_value = "0.7"))]
    pub rst_ccc_thr: f64,

    /// Length of LBD fast EMA         .
    #[cfg_attr(feature = "structopt", structopt(long = "rll", default_value = "50"))]
    pub rst_lbd_len: usize,

    /// Length of LBD slow EMA      .
    #[cfg_attr(
        feature = "structopt",
        structopt(long = "rls", default_value = "10000")
    )]
    pub rst_lbd_slw: usize,

    /// Forcing restart threshold     .
    #[cfg_attr(feature = "structopt", structopt(long = "rlt", default_value = "1.2"))]
    pub rst_lbd_thr: f64,

    /// Usability to restart          .
    #[cfg_attr(feature = "structopt", structopt(long = "rut", default_value = "4.0"))]
    pub rst_mld_thr: f64,

    /// Stabilizer scaling            .
    #[cfg_attr(feature = "structopt", structopt(long = "rss", default_value = "2.0"))]
    pub rst_stb_scl: f64,

    //
    //## vivifier
    //
    /// Lower bound of vivif. loop    .
    #[cfg_attr(feature = "structopt", structopt(long = "vib", default_value = "1.0"))]
    pub viv_beg: f64,

    /// Upper bound of vivif. loop    .
    #[cfg_attr(feature = "structopt", structopt(long = "vie", default_value = "2.0"))]
    pub viv_end: f64,

    /// Vivification interval           .
    #[cfg_attr(feature = "structopt", structopt(long = "vii", default_value = "4"))]
    pub viv_int: usize,

    /// #reduction for next vivif.    .
    #[cfg_attr(feature = "structopt", structopt(long = "vis", default_value = "2.0"))]
    pub viv_scale: f64,

    //
    //## var rewarding
    //
    /// Initial var reward decay     .
    #[cfg_attr(feature = "structopt", structopt(long = "vri", default_value = "0.75"))]
    pub vrw_dcy_beg: f64,

    /// Maximum var reward decay     .
    #[cfg_attr(feature = "structopt", structopt(long = "vrm", default_value = "0.98"))]
    pub vrw_dcy_end: f64,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            a_adaptive: 1,
            a_elim: 1,
            a_reduce: 1,
            a_rephase: 1,
            a_rsr: 1,
            a_stabilize: 1,
            a_vivify: 1,

            c_cbt_thr: 100,
            c_cls_lim: 0,
            c_ip_int: 25000,
            c_tout: 5000.0,

            splr_interface: false,
            cnf_file: PathBuf::new(),
            io_dump: 0,
            io_odir: PathBuf::new(),
            io_pfile: PathBuf::new(),
            io_rfile: PathBuf::new(),
            no_color: true,
            quiet_mode: true,
            use_certification: false,
            use_log: false,

            elim_cls_lim: 32,
            elim_grw_lim: 0,
            elim_var_occ: 8192,

            rst_step: 50,
            rst_asg_len: 50,
            rst_asg_slw: 10000,
            rst_asg_thr: 1.40,
            rst_ccc_thr: 0.70,
            rst_lbd_len: 50,
            rst_lbd_slw: 10000,
            rst_lbd_thr: 1.20,
            rst_mld_thr: 4.00,
            rst_stb_scl: 2.0,

            viv_beg: 1.0,
            viv_end: 2.0,
            viv_int: 4,
            viv_scale: 2.0,

            vrw_dcy_beg: 0.75,
            vrw_dcy_end: 0.98,
        }
    }
}

impl<T> From<T> for Config
where
    PathBuf: From<T>,
{
    #[cfg(not(feature = "structopt"))]
    fn from(path: T) -> Config {
        Config {
            cnf_file: PathBuf::from(path),
            ..Config::default()
        }
    }
    #[cfg(feature = "structopt")]
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
        dispatch!(self.a_reduce)
    }
    pub fn use_elim(&self) -> bool {
        dispatch!(self.a_elim)
    }
    pub fn use_vivify(&self) -> bool {
        dispatch!(self.a_vivify)
    }
    pub fn use_rephase(&self) -> bool {
        dispatch!(self.a_rephase)
    }
    pub fn use_reason_side_rewarding(&self) -> bool {
        dispatch!(self.a_rsr)
    }
    pub fn use_stabilize(&self) -> bool {
        dispatch!(self.a_stabilize)
    }
    pub fn use_adaptive(&self) -> bool {
        dispatch!(self.a_adaptive)
    }
}

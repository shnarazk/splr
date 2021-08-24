/// Crate `config` provides solver's configuration and CLI.
use {crate::types::DecisionLevel, std::path::PathBuf};

pub const CERTIFICATION_DEFAULT_FILENAME: &str = "proof.drat";

/// Configuration built from command line options
#[derive(Clone, Debug)]
pub struct Config {
    //
    //## solver configuration
    //
    /// Dec. lvl to use chronoBT
    pub c_cbt_thr: DecisionLevel,

    /// Soft limit of #clauses (6MC/GB)
    pub c_cls_lim: usize,

    /// #cls to start in-processor
    pub c_ip_int: usize,

    /// CPU time limit in sec.
    pub c_timeout: f64,

    //
    //## I/O configuration
    //
    /// Build Splr interface
    pub splr_interface: bool,

    /// DIMACS CNF file
    pub cnf_file: PathBuf,

    /// Output directory
    pub io_odir: PathBuf,

    /// DRAT Cert. filename
    pub io_pfile: PathBuf,

    /// Result filename/stdout
    pub io_rfile: PathBuf,

    /// Disable coloring
    pub no_color: bool,

    /// Disable any progress message
    pub quiet_mode: bool,

    /// Show sub-module logging report
    pub show_journal: bool,

    /// Writes a DRAT UNSAT certification file
    pub use_certification: bool,

    /// Uses Glucose-like progress report
    pub use_log: bool,

    //
    //## clause rewarding
    //
    pub crw_dcy_rat: f64,

    //
    //## eliminator
    //
    /// Max #lit for clause subsume
    pub elm_cls_lim: usize,

    /// Grow limit of #cls in var elimination
    pub elm_grw_lim: usize,

    /// Max #cls for var elimination
    pub elm_var_occ: usize,

    //
    //## restarter
    //
    /// #conflicts between restarts
    pub rst_step: usize,

    /// Length of assign. fast EMA
    pub rst_asg_len: usize,

    /// Length of assign. slow EMA
    pub rst_asg_slw: usize,

    /// Blocking restart threshold. Originally this was the Glucose's R.
    pub rst_asg_thr: f64,

    /// Length of LBD fast EMA
    pub rst_lbd_len: usize,

    /// Length of LBD slow EMA
    pub rst_lbd_slw: usize,

    /// Forcing restart threshold
    pub rst_lbd_thr: f64,

    //
    //## vivifier
    //

    //
    //## var staging
    //
    /// Decay rate of the extra reward for staged vars
    pub stg_rwd_dcy: f64,
    /// Initial value of the extra reward for staged vars
    pub stg_rwd_val: f64,

    //
    //## var rewarding
    //
    /// Var Reward Decay Rate
    pub vrw_dcy_rat: f64,
    /// Decay increment step.
    pub vrw_dcy_stp: f64,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            c_cbt_thr: 100,
            c_cls_lim: 0,
            c_ip_int: 10000,
            c_timeout: 5000.0,

            splr_interface: false,
            cnf_file: PathBuf::new(),
            io_odir: PathBuf::from("."),
            io_pfile: PathBuf::from(CERTIFICATION_DEFAULT_FILENAME),
            io_rfile: PathBuf::new(),
            no_color: false,
            quiet_mode: false,
            show_journal: false,
            use_certification: false,
            use_log: false,

            crw_dcy_rat: 0.95,

            elm_cls_lim: 18,
            elm_grw_lim: 0,
            elm_var_occ: 20000,

            rst_step: 2,
            rst_asg_len: 16,
            rst_asg_slw: 8192,
            rst_asg_thr: 0.6,
            rst_lbd_len: 8,
            rst_lbd_slw: 8192,
            rst_lbd_thr: 1.4,

            stg_rwd_dcy: 0.5,
            stg_rwd_val: 1.0,

            #[cfg(feature = "EVSIDS")]
            vrw_dcy_rat: 0.98,
            #[cfg(feature = "LR_rewarding")]
            vrw_dcy_rat: 0.96,
            #[cfg(feature = "EVSIDS")]
            vrw_dcy_stp: 0.0001,
            #[cfg(feature = "LR_rewarding")]
            vrw_dcy_stp: 0.0,
        }
    }
}

impl Config {
    pub fn inject_from_args(&mut self) {
        let mut help = false;
        let mut version = false;
        if 1 < std::env::args().count() {
            if let Some(ref cnf) = std::env::args().last() {
                // we'll check the existence after parsing all args.
                self.cnf_file = PathBuf::from(cnf.clone());
            }
        }
        let args = std::env::args();
        let mut iter = args.skip(1);
        while let Some(arg) = iter.next() {
            if let Some(stripped) = arg.strip_prefix("--") {
                let flags = [
                    "no-color", "quiet", "certify", "journal", "log", "help", "version",
                ];
                let options_u32 = ["cbt"];
                let options_usize = [
                    "cl", "ii", "stat", "ecl", "evl", "evo", "rs", "ral", "ras", "rll", "rls",
                ];
                let options_f64 = ["timeout", "cdr", "rat", "rlt", "srd", "srv", "vdr", "vds"];
                let options_path = ["dir", "proof", "result"];
                let seg: Vec<&str> = stripped.split('=').collect();
                match seg.len() {
                    1 => {
                        let name = &arg[2..];
                        if flags.contains(&name) {
                            match name {
                                "no-color" => self.no_color = true,
                                "quiet" => self.quiet_mode = true,
                                "certify" => self.use_certification = true,
                                "journal" => self.show_journal = true,
                                "log" => self.use_log = true,
                                "help" => help = true,
                                "version" => version = true,
                                _ => panic!("invalid flag: {}", name),
                            }
                        } else if options_u32.contains(&name) {
                            if let Some(str) = iter.next() {
                                if let Ok(val) = str.parse::<u32>() {
                                    match name {
                                        "cbt" => self.c_cbt_thr = val,
                                        _ => panic!("invalid option: {}", name),
                                    }
                                } else {
                                    panic!("invalid value {}", name);
                                }
                            } else {
                                panic!("no argument for {}", name);
                            }
                        } else if options_usize.contains(&name) {
                            if let Some(str) = iter.next() {
                                if let Ok(val) = str.parse::<usize>() {
                                    match name {
                                        "cl" => self.c_cls_lim = val,
                                        "ii" => self.c_ip_int = val,
                                        "ecl" => self.elm_cls_lim = val,
                                        "evl" => self.elm_grw_lim = val,
                                        "evo" => self.elm_var_occ = val,
                                        "rs" => self.rst_step = val,
                                        "ral" => self.rst_asg_len = val,
                                        "ras" => self.rst_asg_slw = val,
                                        "rll" => self.rst_lbd_len = val,
                                        "rls" => self.rst_lbd_slw = val,
                                        _ => panic!("invalid option: {}", name),
                                    }
                                } else {
                                    panic!("invalid value {}", name);
                                }
                            } else {
                                panic!("no argument for {}", name);
                            }
                        } else if options_f64.contains(&name) {
                            if let Some(str) = iter.next() {
                                if let Ok(val) = str.parse::<f64>() {
                                    match name {
                                        "timeout" => self.c_timeout = val,
                                        "cdr" => self.crw_dcy_rat = val,
                                        "rat" => self.rst_asg_thr = val,
                                        "rlt" => self.rst_lbd_thr = val,
                                        "srd" => self.stg_rwd_dcy = val,
                                        "srv" => self.stg_rwd_val = val,
                                        "vdr" => self.vrw_dcy_rat = val,
                                        "vds" => self.vrw_dcy_stp = val,

                                        _ => panic!("invalid option: {}", name),
                                    }
                                } else {
                                    panic!("invalid value {}", name);
                                }
                            } else {
                                panic!("no argument for {}", name);
                            }
                        } else if options_path.contains(&name) {
                            if let Some(val) = iter.next() {
                                match name {
                                    "dir" => self.io_odir = PathBuf::from(val),
                                    "proof" => self.io_pfile = PathBuf::from(val),
                                    "result" => self.io_rfile = PathBuf::from(val),
                                    _ => panic!("invalid option: {}", name),
                                }
                            } else {
                                panic!("invalid value {}", name);
                            }
                        } else {
                            panic!("unknown option name {}", name);
                        }
                    }
                    _ => {
                        println!("connected long arg: {:?} = {:?}", seg[0], seg[1]);
                    }
                }
            } else if let Some(name) = arg.strip_prefix('-') {
                let flags = ["C", "q", "c", "j", "l", "h", "V"];
                let options_path = ["o", "p", "r", "t"];
                if flags.contains(&name) {
                    match name {
                        "C" => self.no_color = true,
                        "q" => self.quiet_mode = true,
                        "c" => self.use_certification = true,
                        "j" => self.show_journal = true,
                        "l" => self.use_log = true,
                        "h" => help = true,
                        "V" => version = true,
                        _ => panic!("invalid flag: {}", name),
                    }
                } else if options_path.contains(&name) {
                    if let Some(val) = iter.next() {
                        match name {
                            "o" => self.io_odir = PathBuf::from(val),
                            "p" => self.io_pfile = PathBuf::from(val),
                            "r" => self.io_rfile = PathBuf::from(val),
                            "t" => {
                                self.c_timeout = val.parse::<f64>().expect("-t requires a number")
                            }
                            _ => panic!("invalid option: {}", name),
                        }
                    } else {
                        panic!("no argument for {}", name);
                    }
                } else {
                    panic!("unknown option name {}", name);
                }
            } else if self.cnf_file.to_string_lossy() != arg {
                panic!("invalid argument: {}", arg);
            }
        }
        if help {
            let features = [
                #[cfg(feature = "best_phases_tracking")]
                "best phase tracking",
                #[cfg(feature = "bi_clause_completion")]
                "binary clause completion",
                #[cfg(feature = "clause_elimination")]
                "clause elimination",
                #[cfg(feature = "clause_vivification")]
                "clause vivification",
                #[cfg(feature = "EMA_calibration")]
                "EMA calibration",
                #[cfg(feature = "EVSIDS")]
                "EVSIDS rewarding",
                #[cfg(feature = "incremental_solver")]
                "incremental solver",
                #[cfg(feature = "just_used")]
                "use_just_used_flag",
                #[cfg(feature = "LR_rewarding")]
                "Learning-Rate based rewarding",
                #[cfg(feature = "Luby_restart")]
                "Luby restart",
                #[cfg(feature = "Luby_stabilization")]
                "Luby stabilization",
                #[cfg(feature = "reason_side_rewarding")]
                "reason side rewarding",
                #[cfg(feature = "rephase")]
                "stage-based rephase",
                #[cfg(feature = "strategy_adaptation")]
                "strategy adaptation",
            ];
            println!(
                "{}\nActivated features: {}\n{}",
                env!("CARGO_PKG_DESCRIPTION"),
                features.join(", "),
                help_string()
            );
            std::process::exit(0);
        }
        if version {
            println!("{}", env!("CARGO_PKG_VERSION"));
            std::process::exit(0);
        }
        if self.cnf_file.to_string_lossy().is_empty() {
            println!("No target file specified. Run with '--help' to show help message.");
            std::process::exit(0);
        }
        if !self.cnf_file.exists() {
            println!("{} doesn't exist.", self.cnf_file.to_string_lossy());
            std::process::exit(0);
        }
    }
}

fn help_string() -> String {
    let config = Config::default();
    format!(
        "
USAGE:
  splr [FLAGS] [OPTIONS] <cnf-file>
FLAGS:
  -h, --help                Prints help information
  -C, --no-color            Disable coloring
  -q, --quiet               Disable any progress message
  -c, --certify             Writes a DRAT UNSAT certification file
  -j, --journal             Shows sub-module logs
  -l, --log                 Uses Glucose-like progress report
  -V, --version             Prints version information
OPTIONS (\x1B[000m\x1B[031mred options depend on features in Cargo.toml\x1B[000m):
      --cbt <c-cbt-thr>     Dec. lvl to use chronoBT       {:>10}
      --cdr <crw-dcy-rat>   Clause reward decay rate          {:>10.2}
      --cl <c-cls-lim>      Soft limit of #clauses (6MC/GB){:>10}
      --ii <c-ip-int>       #cls to start in-processor     {:>10}
  -t, --timeout <timeout>   CPU time limit in sec.         {:>10}
      --ecl <elm-cls-lim>   Max #lit for clause subsume    {:>10}
      --evl <elm-grw-lim>   Grow limit of #cls in var elim.{:>10}
      --evo <elm-var-occ>   Max #cls for var elimination   {:>10}
  -o, --dir <io-outdir>     Output directory                {:>10}
  -p, --proof <io-pfile>    DRAT Cert. filename                 {:>10}
  -r, --result <io-rfile>   Result filename/stdout             {:>10}
      --ral <rst-asg-len>   Length of assign. fast EMA     {:>10}
      --ras <rst-asg-slw>   Length of assign. slow EMA     {:>10}
      --rat <rst-asg-thr>   Blocking restart threshold        {:>10.2}
      --rll <rst-lbd-len>   Length of LBD fast EMA         {:>10}
      --rls <rst-lbd-slw>   Length of LBD slow EMA         {:>10}
      --rlt <rst-lbd-thr>   Forcing restart threshold         {:>10.2}
      --rs  <rst-step>      #conflicts between restarts    {:>10}
      --srd <stg-rwd-dcy>   Decay rate for staged var reward  {:>10.2}
      --srv <stg-rwd-val>   Extra reward for staged vars      {:>10.2}
      --vdr <vrw-dcy-rat>   Var reward decay rate             {:>10.2}
      --vds <vrw-dcy-stp>   Var reward decay change step      {:>10.2}
ARGS:
  <cnf-file>    DIMACS CNF file
",
        config.c_cbt_thr,
        config.crw_dcy_rat,
        config.c_cls_lim,
        config.c_ip_int,
        config.c_timeout,
        config.elm_cls_lim,
        config.elm_grw_lim,
        config.elm_var_occ,
        config.io_odir.to_string_lossy(),
        config.io_pfile.to_string_lossy(),
        config.io_rfile.to_string_lossy(),
        config.rst_asg_len,
        config.rst_asg_slw,
        config.rst_asg_thr,
        config.rst_lbd_len,
        config.rst_lbd_slw,
        config.rst_lbd_thr,
        config.rst_step,
        config.stg_rwd_dcy,
        config.stg_rwd_val,
        config.vrw_dcy_rat,
        config.vrw_dcy_stp,
    )
}

impl<T> From<T> for Config
where
    PathBuf: From<T>,
{
    fn from(path: T) -> Config {
        Config {
            cnf_file: PathBuf::from(path),
            ..Config::default()
        }
    }
}

#[allow(unused_macros)]
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
}

pub mod property {
    use super::Config;
    use crate::types::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Tf64 {
        ChronoBtThreshold,
        ClauseRewardDecayRate,
        InprocessorInterval,
        RestartAsgThreshold,
        RestartLbdThreshold,
        VarRewardDecayRate,
    }

    pub const F64S: [Tf64; 6] = [
        Tf64::ChronoBtThreshold,
        Tf64::ClauseRewardDecayRate,
        Tf64::InprocessorInterval,
        Tf64::RestartAsgThreshold,
        Tf64::RestartLbdThreshold,
        Tf64::VarRewardDecayRate,
    ];

    impl PropertyDereference<Tf64, f64> for Config {
        #[inline]
        fn derefer(&self, k: Tf64) -> f64 {
            match k {
                Tf64::ChronoBtThreshold => self.c_cbt_thr as f64,
                Tf64::ClauseRewardDecayRate => self.crw_dcy_rat,
                Tf64::InprocessorInterval => self.c_ip_int as f64,
                Tf64::RestartAsgThreshold => self.rst_asg_thr,
                Tf64::RestartLbdThreshold => self.rst_lbd_thr,
                Tf64::VarRewardDecayRate => self.vrw_dcy_rat,
            }
        }
    }
}

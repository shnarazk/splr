/// Crate `config` provides solver's configuration and CLI.
use {crate::types::DecisionLevel, std::path::PathBuf};

/// Configuration built from command line options
#[derive(Clone, Debug)]
pub struct Config {
    //
    // Switches
    //
    #[cfg(feature = "strategy_adaptation")]
    /// Strategy adaptation switch
    a_adaptive: i32,

    /// Eliminator switch
    a_elim: i32,

    /// Use Luby series forcibly
    a_luby: i32,

    /// Clause reduction switch
    a_reduce: i32,

    /// Re-phase switch
    a_rephase: i32,

    /// Reason-Side Rewarding switch
    a_rsr: i32,

    /// Stabilization switch
    a_stabilize: i32,

    /// Staging
    a_stage: i32,

    /// Vivification switch
    a_vivify: i32,

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

    /// Show submodule logging report
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

    #[cfg(feature = "progress_ACC")]
    /// Conflict Correlation threshold
    pub rst_ccc_thr: f64,

    /// Length of LBD fast EMA
    pub rst_lbd_len: usize,

    /// Length of LBD slow EMA
    pub rst_lbd_slw: usize,

    /// Forcing restart threshold
    pub rst_lbd_thr: f64,

    #[cfg(feature = "progress_MLD")]
    /// Scaling for Maximum LBD of a Dep. graph
    pub rst_mld_scl: f64,

    #[cfg(feature = "progress_MLD")]
    /// Threshold for Maximum LBD of a Dep. graph
    pub rst_mld_thr: f64,

    /// Stabilizer scaling
    pub rst_stb_scl: f64,

    /// Stabilizer expansion scale
    pub rst_stb_exp: f64,

    //
    //## vivifier
    //
    /// #reduction for next vivification
    pub viv_thr: usize,

    //
    //## staging
    //
    /// Decay rate for Extra reward for vars on stage
    pub stg_rwd_dcy: f64,
    /// Initial value for the extra reward for vars on stage
    pub stg_rwd_val: f64,

    //
    //## var rewarding
    //
    #[cfg(not(feature = "moving_var_reward_rate"))]
    pub vrw_dcy_rat: f64,

    #[cfg(feature = "moving_var_reward_rate")]
    /// Initial var reward decay
    pub vrw_dcy_beg: f64,

    #[cfg(feature = "moving_var_reward_rate")]
    /// Maximum var reward decay
    pub vrw_dcy_end: f64,

    /// Occurrence compression rate in LR rewarding
    pub vrw_occ_cmp: f64,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            #[cfg(feature = "strategy_adaptation")]
            a_adaptive: 0,

            a_elim: 1,
            a_luby: 0,
            a_reduce: 1,
            a_rephase: 0,
            a_rsr: 1,
            a_stabilize: 1,
            a_stage: 1,
            a_vivify: 0,

            c_cbt_thr: 100,
            c_cls_lim: 0,
            c_ip_int: 10000,
            c_timeout: 5000.0,

            splr_interface: false,
            cnf_file: PathBuf::new(),
            io_odir: PathBuf::from("."),
            io_pfile: PathBuf::from("proof.out"),
            io_rfile: PathBuf::new(),
            no_color: false,
            quiet_mode: false,
            show_journal: false,
            use_certification: false,
            use_log: false,

            crw_dcy_rat: 0.98,

            elm_cls_lim: 32,
            elm_grw_lim: 0,
            elm_var_occ: 8192,

            rst_step: 24,
            rst_asg_len: 24,
            rst_asg_slw: 8192,
            rst_asg_thr: 0.20,

            #[cfg(feature = "progress_ACC")]
            rst_ccc_thr: 0.7,

            rst_lbd_len: 24,
            rst_lbd_slw: 8192,
            rst_lbd_thr: 1.20,

            #[cfg(feature = "progress_MLD")]
            rst_mld_scl: 0.10,
            #[cfg(feature = "progress_MLD")]
            rst_mld_thr: 0.80,

            rst_stb_exp: 1.0,
            rst_stb_scl: 2.0,

            stg_rwd_dcy: 0.5,
            stg_rwd_val: 1.0,

            viv_thr: 1,

            #[cfg(not(feature = "moving_var_reward_rate"))]
            vrw_dcy_rat: 0.96,
            #[cfg(feature = "moving_var_reward_rate")]
            vrw_dcy_beg: 0.90,
            #[cfg(feature = "moving_var_reward_rate")]
            vrw_dcy_end: 0.96,
            vrw_occ_cmp: 0.50,
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
                let options_i32 = [
                    "ADP", "ELI", "LBY", "RDC", "RPH", "RSR", "STB", "STG", "VIV",
                ];
                let options_u32 = ["cbt"];
                let options_usize = [
                    "cl", "ii", "stat", "ecl", "evl", "evo", "rs", "ral", "ras", "rll", "rls",
                    "vit",
                ];
                #[cfg(not(feature = "moving_var_reward_rate"))]
                let options_f64 = [
                    "timeout", "cdr", "rat", "rct", "rlt", "rms", "rmt", "rse", "rss", "srd",
                    "srv", "vdr", "vro",
                ];
                #[cfg(feature = "moving_var_reward_rate")]
                let options_f64 = [
                    "timeout", "cdr", "rat", "rct", "rlt", "rms", "rmt", "rse", "rss", "srd",
                    "srv", "vri", "vrm", "vro",
                ];
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
                        } else if options_i32.contains(&name) {
                            if let Some(str) = iter.next() {
                                if let Ok(val) = str.parse::<i32>() {
                                    match name {
                                        #[cfg(feature = "strategy_adaptation")]
                                        "ADP" => self.a_adaptive = val,

                                        "ELI" => self.a_elim = val,
                                        "LBY" => self.a_luby = val,
                                        "RDC" => self.a_reduce = val,
                                        "RPH" => self.a_rephase = val,
                                        "RSR" => self.a_rsr = val,
                                        "STB" => self.a_stabilize = val,
                                        "STG" => self.a_stage = val,
                                        "VIV" => self.a_vivify = val,
                                        _ => panic!("invalid option: {}", name),
                                    }
                                } else {
                                    panic!("invalid value {}", name);
                                }
                            } else {
                                panic!("no argument for {}", name);
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
                                        "vit" => self.viv_thr = val,
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

                                        #[cfg(feature = "progress_ACC")]
                                        "rct" => self.rst_ccc_thr = val,

                                        "rlt" => self.rst_lbd_thr = val,

                                        #[cfg(feature = "progress_MLD")]
                                        "rms" => self.rst_mld_scl = val,

                                        #[cfg(feature = "progress_MLD")]
                                        "rmt" => self.rst_mld_thr = val,

                                        "rse" => self.rst_stb_exp = val,
                                        "rss" => self.rst_stb_scl = val,
                                        "srd" => self.stg_rwd_dcy = val,
                                        "srv" => self.stg_rwd_val = val,

                                        #[cfg(not(feature = "moving_var_reward_rate"))]
                                        "vdr" => self.vrw_dcy_rat = val,

                                        #[cfg(feature = "moving_var_reward_rate")]
                                        "vri" => self.vrw_dcy_beg = val,

                                        #[cfg(feature = "moving_var_reward_rate")]
                                        "vrm" => self.vrw_dcy_end = val,

                                        "vro" => self.vrw_occ_cmp = val,
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
            println!("{}\n{}", env!("CARGO_PKG_DESCRIPTION"), help_string());
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
        if version {
            println!("{}", env!("CARGO_PKG_VERSION"));
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
  -j, --journal             Show sub-module logs
  -l, --log                 Uses Glucose-like progress report
  -V, --version             Prints version information
OPTIONS (\x1B[000m\x1B[031mred options depend on features in Cargo.toml\x1B[000m):
      \x1B[000m\x1B[031m--ADP <a-adaptive>    Strategy adaptation switch     {:>10}\x1B[000m
      --ELI <a-elim>        Eliminator switch              {:>10}
      --LBY <a-luby>        Use Luby series for restart    {:>10}
      --RDC <a-reduce>      Clause reduction switch        {:>10}
      --RPH <a-rephase>     Re-phase switch                {:>10}
      --RSR <a-rsr>         Reason-Side Rewarding switch   {:>10}
      --STB <a-stabilize>   Stabilization switch           {:>10}
      --STG <a-stage>       Stage switch                   {:>10}
      --VIV <a-vivify>      Vivification switch            {:>10}
      --cbt <c-cbt-thr>     Dec. lvl to use chronoBT       {:>10}
      --cdr <crw-dcy-rat>   Clause reward decay               {:>10.2}
      --cl <c-cls-lim>      Soft limit of #clauses (6MC/GB){:>10}
      --ii <c-ip-int>       #cls to start in-processor     {:>10}
  -t, --timeout <c-timeout> CPU time limit in sec.         {:>10}
      --ecl <elm-cls-lim>   Max #lit for clause subsume    {:>10}
      --evl <elm-grw-lim>   Grow limit of #cls in var elim.{:>10}
      --evo <elm-var-occ>   Max #cls for var elimination   {:>10}
  -o, --dir <io-odir>       Output directory                {:>10}
  -p, --proof <io-pfile>    DRAT Cert. filename                {:>10}
  -r, --result <io-rfile>   Result filename/stdout             {:>10}
      --ral <rst-asg-len>   Length of assign. fast EMA     {:>10}
      --ras <rst-asg-slw>   Length of assign. slow EMA     {:>10}
      --rat <rst-asg-thr>   Blocking restart threshold        {:>10.2}
      \x1B[000m\x1B[031m--rct <rst-ccc-thr>   Conflict Correlation threshold    {:>10.2}\x1B[000m
      --rll <rst-lbd-len>   Length of LBD fast EMA         {:>10}
      --rls <rst-lbd-slw>   Length of LBD slow EMA         {:>10}
      --rlt <rst-lbd-thr>   Forcing restart threshold         {:>10.2}
      \x1B[000m\x1B[031m--rms <rst-mld-scl>   Scaling for Max LBD of Dep.       {:>10.2}\x1B[000m
      \x1B[000m\x1B[031m--rmt <rst-mld-thr>   Threshold for Max LBD of Dep.     {:>10.2}\x1B[000m
      --rse <rst-stb-exp>   Stabilizer expansion scale        {:>10.2}
      --rss <rst-stb-scl>   Stabilizer scaling                {:>10.2}
      --rs  <rst-step>      #conflicts between restarts    {:>10}
      --srd <stg-rwd-dcy>   Decay rate for staged var reward {:>10.2}
      --srv <stg-rwd-val>   Extra reward for staged vars      {:>10.2}
      --vit <viv-thr>       #clause to try to vivify       {:>10}
      \x1B[000m\x1B[031m--vdr <vrw-dcy-rat>   var reward decay                  {:>10.2}\x1B[000m
      \x1B[000m\x1B[031m--vri <vrw-dcy-beg>   Initial var reward decay          {:>10.2}\x1B[000m
      \x1B[000m\x1B[031m--vrm <vrw-dcy-end>   Maximum var reward decay          {:>10.2}\x1B[000m
      \x1B[000m\x1B[031m--vro <vrw-occ-cmp>   Occ. compression rate in LR       {:>10.2}\x1B[000m
ARGS:
  <cnf-file>    DIMACS CNF file
",
        {
            #[cfg(not(feature = "strategy_adaptation"))]
            {
                0.0
            }
            #[cfg(feature = "strategy_adaptation")]
            {
                config.a_adaptive
            }
        },
        config.a_elim,
        config.a_luby,
        config.a_reduce,
        config.a_rephase,
        config.a_rsr,
        config.a_stabilize,
        config.a_stage,
        config.a_vivify,
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
        {
            #[cfg(not(feature = "progress_ACC"))]
            {
                0.0
            }
            #[cfg(feature = "progress_ACC")]
            {
                config.rst_ccc_thr
            }
        },
        config.rst_lbd_len,
        config.rst_lbd_slw,
        config.rst_lbd_thr,
        {
            #[cfg(feature = "progress_MLD")]
            {
                config.rst_mld_scl
            }
            #[cfg(not(feature = "progress_MLD"))]
            {
                0.0
            }
        },
        {
            #[cfg(feature = "progress_MLD")]
            {
                config.rst_mld_thr
            }
            #[cfg(not(feature = "progress_MLD"))]
            {
                0.0
            }
        },
        config.rst_stb_exp,
        config.rst_stb_scl,
        config.rst_step,
        config.stg_rwd_dcy,
        config.stg_rwd_val,
        config.viv_thr,
        {
            #[cfg(not(feature = "moving_var_reward_rate"))]
            {
                config.vrw_dcy_rat
            }
            #[cfg(feature = "moving_var_reward_rate")]
            {
                0.0
            }
        },
        {
            #[cfg(not(feature = "moving_var_reward_rate"))]
            {
                0.0
            }
            #[cfg(feature = "moving_var_reward_rate")]
            {
                config.vrw_dcy_beg
            }
        },
        {
            #[cfg(not(feature = "moving_var_reward_rate"))]
            {
                0.0
            }
            #[cfg(feature = "moving_var_reward_rate")]
            {
                config.vrw_dcy_end
            }
        },
        {
            #[cfg(not(feature = "moving_var_reward_rate"))]
            {
                0.0
            }
            #[cfg(feature = "moving_var_reward_rate")]
            {
                config.vrw_occ_cmp
            }
        },
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
    pub fn use_elim(&self) -> bool {
        dispatch!(self.a_elim)
    }
    pub fn use_luby(&self) -> bool {
        dispatch!(self.a_luby)
    }
    pub fn use_reduce(&self) -> bool {
        dispatch!(self.a_reduce)
    }
    pub fn use_rephase(&self) -> bool {
        dispatch!(self.a_rephase)
    }
    pub fn use_vivify(&self) -> bool {
        dispatch!(self.a_vivify)
    }
    pub fn use_reason_side_rewarding(&self) -> bool {
        dispatch!(self.a_rsr)
    }
    pub fn use_stabilize(&self) -> bool {
        dispatch!(self.a_stabilize)
    }
    pub fn use_stage(&self) -> bool {
        dispatch!(self.a_stage)
    }
    #[cfg(feature = "strategy_adaptation")]
    pub fn use_adaptive(&self) -> bool {
        dispatch!(self.a_adaptive)
    }
}

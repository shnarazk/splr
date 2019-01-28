// SAT solver for Propositional Logic in Rust
// Version 0.0.13 (Technology Preview 13) by shnarazk@gitlab.com

use splr::config::Config;
use splr::solver::{Certificate, Solver};
use splr::traits::SatSolverIF;
use std::fs::File;
use std::io::{BufWriter, Write};
use structopt::StructOpt;

#[derive(StructOpt)]
#[structopt(
    name = "splr",
    about = "SAT solver for Propositional Logic in Rust, Technology Preview 13"
)]
struct CLOpts {
    /// EMA coefficient for number of assignments
    #[structopt(long = "ra", default_value = "3500")]
    restart_asg_samples: usize,
    /// EMA coefficient for learnt clause LBD
    #[structopt(long = "rl", default_value = "50")]
    restart_lbd_samples: usize,
    /// K in Glucose, for restart
    #[structopt(long = "rt", default_value = "0.80")]
    restart_threshold: f64,
    /// R in Glucose, for blocking
    #[structopt(long = "rb", default_value = "1.40")]
    restart_blocking: f64,
    /// Minimal stpes between restart
    #[structopt(long = "rs", default_value = "50")]
    restart_step: usize,
    /// Uses another format for progress report
    #[structopt(long = "--log", short = "l")]
    use_log: bool,
    /// Disables clause/variable elimination
    #[structopt(long = "no-elim", short = "e")]
    no_elim: bool,
    /// Disables dynamic strategy adaptation
    #[structopt(long = "no-adaptation", short = "a")]
    no_adapt: bool,
    /// a CNF file to solve
    #[structopt(parse(from_os_str))]
    cnf: std::path::PathBuf,
}

fn main() {
    let args = CLOpts::from_args();
    if args.cnf.exists() {
        let mut config = Config::default();
        config.adapt_strategy = !args.no_adapt;
        config.restart_thr = args.restart_threshold;
        config.restart_blk = args.restart_blocking;
        config.restart_asg_len = args.restart_asg_samples;
        config.restart_lbd_len = args.restart_lbd_samples;
        config.restart_step = args.restart_step;
        config.progress_log = args.use_log;
        if args.no_elim {
            config.use_elim = false;
        }
        let (mut s, _cnf) = Solver::build(config, &args.cnf.to_str().unwrap());
        let result = format!(".ans_{}", args.cnf.file_name().unwrap().to_str().unwrap());
        match s.solve() {
            Ok(Certificate::SAT(v)) => {
                if let Ok(out) = File::create(&result) {
                    let mut buf = BufWriter::new(out);
                    for x in &v {
                        if let Err(why) = buf.write(format!("{} ", x).as_bytes()) {
                            panic!("failed to save: {:?}!", why);
                        }
                    }
                    if let Err(why) = buf.write(b"0\n") {
                        panic!("failed to save: {:?}!", why);
                    }
                }
                println!(
                    "SATISFIABLE: {}. The answer was dumped to {}.",
                    s.state.target.pathname,
                    result.as_str()
                );
                // println!("{:?}", v);
            }
            Ok(Certificate::UNSAT(_)) => {
                if let Ok(mut out) = File::create(&result) {
                    if let Err(why) = out.write_all(b"[]\n") {
                        panic!("failed to save: {:?}!", why);
                    }
                }
                println!(
                    "UNSAT: {}, The answer was dumped to {}.",
                    s.state.target.pathname,
                    result.as_str()
                );
            }
            Err(_) => println!("Failed"),
        }
    } else {
        println!(
            "{} does not exist.",
            args.cnf.file_name().unwrap().to_str().unwrap()
        );
    }
}

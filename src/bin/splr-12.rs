// SAT solver for Propositional Logic in Rust
use splr::config::SolverConfig;
use splr::solver::{Certificate, Solver};
use splr::traits::SatSolver;
use std::fs::File;
use std::io::{BufWriter, Write};
use structopt::StructOpt;

// const VERSION: &str = "Splr-0.0.12 (Technology Preview 12) by shnarazk@gitlab.com";

#[derive(StructOpt)]
#[structopt(
    name = "splr",
    about = "SAT solver for Propositional Logic in Rust, Technology Preview 12"
)]
struct CLOpts {
    /// EMA coefficient for number of assignments
    #[structopt(long = "ra", default_value = "3500")]
    restart_asg_samples: usize,
    /// EMA coefficient for learnt clause LBD
    #[structopt(long = "rl", default_value = "50")]
    restart_lbd_samples: usize,
    /// K in Glucose, for restart
    #[structopt(long = "rt", default_value = "0.75")]
    restart_threshold: f64,
    /// R in Glucose, for blocking
    #[structopt(long = "rb", default_value = "1.40")]
    restart_blocking: f64,
    /// Dump progress report in another format
    #[structopt(long = "--log", short = "l")]
    use_log: bool,
    /// Don't use clause/variable eliminator
    #[structopt(long = "no-elim", short = "e")]
    no_elim: bool,
    /// Don't use dynamic strategy adaptation
    #[structopt(long = "no-adaptation", short = "a")]
    no_adapt: bool,
    /// a CNF file to solve
    #[structopt(parse(from_os_str))]
    cnf: std::path::PathBuf,
}

fn main() {
    let args = CLOpts::from_args();
    if args.cnf.exists() {
        let mut config = SolverConfig::default();
        config.adapt_strategy = !args.no_adapt;
        config.restart_thr = args.restart_threshold;
        config.restart_blk = args.restart_blocking;
        config.restart_asg_len = args.restart_asg_samples;
        config.restart_lbd_len = args.restart_lbd_samples;
        config.progress_log = args.use_log;
        if args.no_elim {
            config.use_sve = false;
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
                println!("SATISFIABLE. The answer was dumped to {}.", result.as_str());
                // println!("{:?}", v);
            }
            Ok(Certificate::UNSAT(_)) => {
                if let Ok(mut out) = File::create(&result) {
                    if let Err(why) = out.write_all(b"[]\n") {
                        panic!("failed to save: {:?}!", why);
                    }
                }
                println!("UNSAT, The answer was dumped to {}.", result.as_str());
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

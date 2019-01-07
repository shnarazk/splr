// SAT solver for Propositional Logic in Rust
use splr::solver::{Certificate, Solver};
use splr::traits::SatSolver;
use std::fs::File;
use std::io::{BufWriter, Write};
use structopt::StructOpt;

// const VERSION: &str = "Splr-0.0.12 (Technology Preview 12) by shnarazk@gitlab.com";

#[derive(StructOpt)]
#[structopt(
    name = "splr-12",
    about = "SAT solver for Propositional Logic in Rust, Technology Preview 12"
)]
struct CLOpts {
    /// K in Glucose, for restart
    #[structopt(long = "rt", short = "K", default_value = "0.8")]
    restart_threshold: f64,
    /// R in Glucose, for blocking
    #[structopt(long = "rb", short = "R", default_value = "1.40")]
    restart_blocking: f64,
    #[structopt(long = "no-tty", short = "t")]
    no_tty: bool,
    #[structopt(long = "no-elim", short = "e")]
    no_elim: bool,
    #[structopt(long = "no-adaptation", short = "a")]
    no_adapt: bool,
    #[structopt(parse(from_os_str))]
    cnf: std::path::PathBuf,
}

fn main() {
    let args = CLOpts::from_args();
    if args.cnf.exists() {
        let (mut s, _cnf) = Solver::build(&args.cnf.to_str().unwrap());
        let result = format!(".ans_{}", args.cnf.file_name().unwrap().to_str().unwrap());
        if args.no_tty {
            s.config.use_tty = false;
        }
        if args.no_elim {
            s.elim.use_elim = false;
        }
        s.config.adapt_strategy = !args.no_adapt;
        s.config.restart_thr = args.restart_threshold;
        s.config.restart_blk = args.restart_blocking;
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
                println!("[]");
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

// SAT solver for Propositional Logic in Rust
use splr::solver::{Certificate, SatSolver, Solver};
use std::fs::File;
use std::io::{BufWriter, Write};
use structopt::StructOpt;

// const VERSION: &str = "Splr-0.0.11 (Technology Preview 11) by shnarazk@gitlab.com";

#[derive(StructOpt)]
#[structopt(name = "splr", about = "SAT solver for Propositional Logic in Rust, Technology Preview 11")]
struct CLOpts {
    #[structopt(long = "forcing-restart", short="K")]
    k: Option<f64>,
    #[structopt(long = "blocking-restart", short="R")]
    r: Option<f64>,
    #[structopt(long = "tty", short="t")]
    no_tty: bool,
    #[structopt(long = "elim", short="e")]
    no_elim: bool,
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
            s.eliminator.use_elim = false; 
        }
        if let Some(k) = args.k {
            println!("This version can't handle '-K {:>4.2}'.", k);
        }
        if let Some(r) = args.r {
            println!("This version can't handle '-R {:>4.2}'.", r);
        }
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
        println!("{} does not exist.", args.cnf.file_name().unwrap().to_str().unwrap());
    }
}

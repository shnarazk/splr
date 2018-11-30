extern crate splr;
use splr::solver::{Certificate, SatSolver, Solver};
use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;
use std::process::exit;

const VERSION: &str = "Splr-0.0.11 (Technology Preview 11) by shnarazk@gitlab.com";

fn main() {
    let mut target: Option<String> = None;
    let args: Vec<String> = env::args().skip(1).collect();
    for arg in &args {
        match arg {
            _ if arg == "--version" => {
                println!("{}", VERSION);
            }
            _ if (&*arg).starts_with('-') => {
                if arg == "--help" {
                    println!("splr [CNF|--version|--help]");
                    exit(0);
                }
                continue;
            }
            _ => {
                target = Some(arg.to_string());
            }
        }
    }
    if let Some(path) = target {
        let file = Path::new(&path);
        let (mut s, _cnf) = Solver::build(&path);
        let result = format!(".ans_{}", file.file_name().unwrap().to_str().unwrap());
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
            Err(e) => println!("Failed {:?}", e),
        }
    }
}

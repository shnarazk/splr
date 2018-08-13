extern crate splr;
use splr::search::SolveSAT;
use splr::solver::*;
use std::env;

fn main() {
    // println!("splr 0.0.1 CARGO_MANIFEST_DIR = {}", env!("CARGO_MANIFEST_DIR"));
    // Some(env!("CARGO_MANIFEST_DIR").to_string() + "/uf200-020.cnf");
    let mut target: Option<String> = None;
    let args: Vec<String> = env::args().skip(1).collect();
    for arg in &args {
        match arg {
            _ if arg.to_string() == "--version" => {
                println!("Splr 0.0.1");
            }
            _ if (&*arg).starts_with('-') => {
                continue;
            }
            _ => {
                target = Some(arg.to_string());
            }
        }
    }
    if let Some(path) = target {
        let (mut s, _cnf) = Solver::build(&path);
        match s.solve() {
            Ok(Certificate::SAT(v)) => println!("{:?}", v),
            Ok(Certificate::UNSAT(v)) => println!("UNSAT {:?}", v),
            Err(e) => println!("Failed {:?}", e),
        }
    }
}

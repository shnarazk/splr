extern crate splr;
use splr::search::SolveSAT;
use splr::solver::*;
use splr::types::*;
use std::env;

fn main() {
    // println!("splr 0.0.1 CARGO_MANIFEST_DIR = {}", env!("CARGO_MANIFEST_DIR"));
    let mut target: String = env!("CARGO_MANIFEST_DIR").to_string() + "/uf200-020.cnf";
    let args: Vec<String> = env::args().skip(1).collect();
    for arg in &args {
        match arg {
            _ if arg.to_string() == "--version" => {
                println!("0.0.1");
                return;
            }
            _ if (&*arg).starts_with('-') => {
                continue;
            }
            _ => {
                target = arg.to_string();
            }
        }
    }
    // println!("Hello, world! {}", target);
    let (mut s, _cnf) = Solver::build(&target);
    match s.solve() {
        Ok(Certificate::SAT(v)) => println!("{:?}", v),
        Ok(Certificate::UNSAT(v)) => println!("UNSAT {:?}", v),
        Err(e) => println!("Failed {:?}", e),
    }
}

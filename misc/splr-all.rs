#![cfg(feature = "incremental_solver")]
///```ignore
/// cargo run --example splr-incremental -- a.cnf
///```
use splr::*;
use std::env::args;

fn main() {
    let cnf = args().nth(1).expect("takes an arg");
    let ns = run(&cnf);
    println!("#solution: {}", ns);
}

fn run(cnf: &str) -> usize {
    let mut solver = Solver::try_from(cnf).expect("panic");
    let mut count = 0;
    for _res in solver.iter() {
        count += 1;
        println!("s SATISFIABLE({})", count);
    }
    count
}

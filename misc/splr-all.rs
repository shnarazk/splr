#![cfg(feature = "incremental_solver")]
/// All solutions solver implementation based on feature 'incremental solver'
/// But the main purpose is to check the correctness of the implementaion of
/// feature 'incremental solver'.
///
/// To run me:
///```ignore
/// cargo run --example splr-incremental -- a.cnf
///```
use splr::*;
use std::env::args;

fn main() {
    let cnf_file = args().nth(1).expect("takes an arg");
    let ns = run(&cnf_file);
    println!("#solution: {}", ns);
}

fn run(cnf_file: &str) -> usize {
    let mut solver = Solver::try_from(cnf_file).expect("panic");
    // let cnf = solver.state.config.cnf();
    let mut count = 0;
    let mut solutions = Vec::new();
    for res in solver.iter() {
        solutions.push(res);
        count += 1;
        println!("s SATISFIABLE({})", count);
        // dump_refuting_cnf(cnf, res);
    }
    count
}

// fn dump_refuting_cnf(cnf: CNF, clause: Vec<i32>) {
//     todo!();
// }

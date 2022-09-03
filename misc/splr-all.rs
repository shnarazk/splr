#![cfg(feature = "incremental_solver")]
use ::cnf::*;
use splr::*;
use std::env::args;
/// All solutions solver implementation based on feature 'incremental solver'
/// But the main purpose is to check the correctness of the implementaion of
/// feature 'incremental solver'.
///
/// To run me:
///```ignore
/// cargo run --example all-solutions -- a.cnf
///```

fn main() {
    let cnf_file = args().nth(1).expect("takes an arg");
    let ns = run(&cnf_file);
    println!("#solution: {}", ns);
}

fn run(cnf_file: &str) -> usize {
    let mut cnf = CNF::load(&std::path::PathBuf::from(cnf_file)).expect("fail to load");
    println!("{cnf}");
    let mut solver = Solver::try_from(cnf_file).expect("panic");
    let mut count = 0;
    let mut solutions = Vec::new();
    for res in solver.iter() {
        count += 1;
        let refuter: Vec<i32> = res.iter().map(|l| -l).collect::<Vec<_>>();
        solutions.push(res);
        cnf.add_clause(refuter).expect("An internal error");
        println!("s SATISFIABLE({count}) => {cnf}");
    }
    // cnf.save(???);???;
    count
}

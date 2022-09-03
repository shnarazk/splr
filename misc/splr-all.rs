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
    run(&cnf_file);
}

fn run(cnf_file: &str) -> Vec<Vec<i32>> {
    let path = std::path::PathBuf::from(cnf_file);
    let name = path.file_stem().expect("It seems a strange filename");
    let mut cnf = CNF::load(&path).expect("fail to load");
    println!("{cnf}");
    let mut solver = Solver::try_from(cnf_file).expect("panic");
    let mut count = 0;
    let mut solutions = Vec::new();
    for res in solver.iter() {
        count += 1;
        let refuter: Vec<i32> = res.iter().map(|l| -l).collect::<Vec<_>>();
        solutions.push(res);
        cnf.add_clause(refuter).expect("An internal error");
        let dump_name = format!("{}-refuting-{count}.cnf", name.to_string_lossy());
        let dump = std::path::PathBuf::from(&dump_name);
        cnf.save(&dump).expect("???");
        println!("s SATISFIABLE({count}) => {dump_name}");
    }
    let dump_name = format!("{}-refuting-all{count}.cnf", name.to_string_lossy());
    let dump = std::path::PathBuf::from(&dump_name);
    cnf.save(&dump).expect("???");
    println!("#solution: {count} => {dump_name}");
    solutions
}

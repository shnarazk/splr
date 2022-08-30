#![cfg(feature = "incremental_solver")]
/// WARNING: this test requires feature "incremental_solver".
///```ignore
/// cargo test --test isat2 --features incremental_solver --release -- --nocapture --test-threads=1
///```
use splr::*;
use std::env::args;

fn main() {
    let cnf = args().nth(1).expect("takes an arg");
    let assumptions = Vec::new();
    let ns1 = run(&cnf, &assumptions, false);
    let ns2 = run(&cnf, &assumptions, true);
    println!("#solution: {} w/o elim; {} w/ elim", ns1, ns2);
}

#[test]
fn all_solutions_of_uf8() {
    drive("cnfs/uf8.cnf", vec![4, 5, -6, 7, 8]);
}

#[test]
fn all_solutions_of_uf20() {
    drive("cnfs/uf20-01.cnf", vec![-4, 5, 6, 7, 8]);
}

#[allow(dead_code)]
/// cargo test --test isat2 --features incremental_solver --release
/// #[cfg_attr(feature = "incremental_solver", test)]
fn all_solutions_of_uf100() {
    drive("cnfs/uf100-010.cnf", vec![]);
}

fn drive(cnf: &str, mother: Vec<i32>) {
    for i in 0..=mother.len() {
        let assumptions = &mother[0..i];
        let ns1 = run(cnf, assumptions, false);
        let ns2 = run(cnf, assumptions, true);
        println!("#solution: {} w/o elim; {} w/ elim", ns1, ns2);
        assert_eq!(ns1, ns2);
    }
}

fn run(cnf: &str, assigns: &[i32], switch: bool) -> usize {
    println!("-------------------- {:?}, {}", assigns, switch);
    let mut solver = Solver::try_from(cnf).expect("panic");
    // solver.state.config.enable_eliminator = switch;
    for n in assigns.iter() {
        solver.add_assignment(*n).expect("no");
    }
    let mut count = 0;
    for res in solver.iter() {
        count += 1;
        println!("s SATISFIABLE({}): {:?}", count, res);
    }
    count
}

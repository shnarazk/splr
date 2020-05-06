/// WARNING: this test requires feature "incremental_solver".
///```ignore
/// cargo test --test isat2 --features incremental_solver --release -- --nocapture --test-threads=1
///```
use splr::*;
use std::{convert::TryFrom, env::args};

#[cfg(feature = "incremental_solver")]
fn main() {
    let cnf = args().nth(1).expect("takes an arg");
    let assumptions = Vec::new();
    let ns1 = run(&cnf, &assumptions, false);
    let ns2 = run(&cnf, &assumptions, true);
    println!("#solution: {} w/o elim; {} w/ elim", ns1, ns2);
}

#[allow(dead_code)]
#[cfg(feature = "incremental_solver")]
#[cfg_attr(feature = "incremental_solver", test)]
fn all_solutions_of_uf8() {
    drive("tests/uf8.cnf", vec![4, 5, -6, 7, 8]);
}

#[allow(dead_code)]
#[cfg(feature = "incremental_solver")]
#[cfg_attr(feature = "incremental_solver", test)]
fn all_solutions_of_uf20() {
    drive("tests/uf20-01.cnf", vec![-4, 5, 6, 7, 8]);
}

#[allow(dead_code)]
#[cfg(feature = "incremental_solver")]
/// cargo test --test isat2 --features incremental_solver --release
/// #[cfg_attr(feature = "incremental_solver", test)]
fn all_solutions_of_uf100() {
    drive("tests/uf100-010.cnf", vec![]);
}

#[cfg(feature = "incremental_solver")]
fn drive(cnf: &str, mother: Vec<i32>) {
    for i in 0..=mother.len() {
        let assumptions = &mother[0..i];
        let ns1 = run(&cnf, &assumptions, false);
        let ns2 = run(&cnf, &assumptions, true);
        println!("#solution: {} w/o elim; {} w/ elim", ns1, ns2);
        assert_eq!(ns1, ns2);
    }
}

#[cfg(feature = "incremental_solver")]
fn run(cnf: &str, assigns: &[i32], switch: bool) -> usize {
    println!("-------------------- {:?}, {}", assigns, switch);
    let mut solver = Solver::try_from(cnf).expect("panic");
    solver.elim.enable = switch;
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

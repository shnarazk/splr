#![cfg(feature = "incremental_solver")]
/// WARNING: this test requires feature "incremental_solver".
///```ignore
/// cargo test --test isat --features incremental_solver --release -- --nocapture --test-threads=1
///```
use splr::*;
use std::{env::args, path::Path};

fn main() {
    let cnf = args().nth(1).expect("takes an arg");
    let assumptions = Vec::new();
    let ns1 = run(Path::new(&cnf), &assumptions, false);
    let ns2 = run(Path::new(&cnf), &assumptions, true);
    println!("#solution: {} w/o elim; {} w/ elim", ns1, ns2);
}

#[test]
fn all_solutions_of_uf8() {
    drive(Path::new("cnfs/uf8.cnf"), vec![4, 5, -6, 7, 8]);
}

#[test]
fn all_solutions_of_uf20() {
    drive(Path::new("cnfs/uf20-01.cnf"), vec![-4, 5, 6, 7, 8]);
}

#[allow(dead_code)]
/// cargo test --test isat --features incremental_solver --release
fn all_solutions_of_uf100() {
    drive(Path::new("cnfs/uf100-010.cnf"), vec![]);
}

fn drive(cnf: &Path, mother: Vec<i32>) {
    for i in 0..=mother.len() {
        let assumptions = &mother[0..i];
        let ns1 = run(cnf, assumptions, false);
        let ns2 = run(cnf, assumptions, true);
        println!("#solution: {} w/o elim; {} w/ elim", ns1, ns2);
        debug_assert_eq!(ns1, ns2);
    }
}

#[cfg(not(feature = "no_IO"))]
fn run(cnf: &Path, assigns: &[i32], switch: bool) -> usize {
    println!("-------------------- {:?}, {}", assigns, switch);
    let mut solver = Solver::try_from(cnf).expect("panic");
    // solver.state.config.enable_eliminator = switch;
    for n in assigns.iter() {
        solver.add_assignment(*n).expect("no");
    }
    let mut count = 0;
    loop {
        match solver.solve() {
            Ok(Certificate::SAT(mut ans)) => {
                count += 1;
                println!("s SATISFIABLE({}): {:?}", count, ans);

                //
                // Run an external validator
                //
                {
                    let mut validator = Solver::try_from(cnf).expect("panic");
                    validator
                        .inject_assignment(&ans)
                        .expect("It's completely broken!");
                    if let Some(v) = validator.validate() {
                        panic!("It's an invalid assignment against clause {:?}.", v);
                    }
                }

                for i in ans.iter_mut() {
                    *i *= -1;
                }
                // Or you can build a new clause which literals are flipped.
                // let ans: Vec<i32> = ans.iter().map(|i| -i).collect::<Vec<i32>>();
                assert!(1 < ans.len());
                match solver.add_clause(ans.clone()) {
                    Err(SolverError::Inconsistent) => {
                        println!("c no (more) answer due to level zero conflict");
                        break;
                    }
                    Err(SolverError::EmptyClause) => {
                        println!("c no (more) answer due to an empty clause");
                        break;
                    }
                    Err(e) => {
                        println!("s UNKNOWN; {:?} by {:?}", e, ans);
                        break;
                    }
                    Ok(_) => solver.reset(),
                }
            }
            Ok(Certificate::UNSAT) => {
                println!("s UNSATISFIABLE");
                break;
            }
            Err(e) => {
                println!("s UNKNOWN; {}", e);
                break;
            }
        }
    }
    count
}

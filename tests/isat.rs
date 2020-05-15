/// WARNING: this test requires feature "incremental_solver".
use splr::*;
#[allow(unused_imports)]
use std::{convert::TryFrom, env::args};

#[cfg(feature = "incremental_solver")]
#[test]
fn main() {
    let cnf = "tests/uf8.cnf"; // args().nth(1).expect("takes a arg");
    let v: Vec<i32> = vec![8, 7, -6, 5, 4];
    let ns1 = run(cnf, &v, false);
    let ns2 = run(cnf, &v, true);
    println!("#solution: {} w/o elim; {} w/ elim", ns1, ns2);
    assert_eq!(ns1, ns2);
}

#[allow(dead_code)]
fn run(cnf: &str, assigns: &[i32], switch: bool) -> usize {
    println!("-------------------- {:?}, {}", assigns, switch);
    let mut solver = Solver::try_from(cnf).expect("panic");
    solver.elim.enable = switch;
    for n in assigns.iter() {
        solver.add_assignment(*n).expect("no");
    }
    let mut count = 0;
    loop {
        match solver.solve() {
            Ok(Certificate::SAT(mut ans)) => {
                count += 1;
                println!("s SATISFIABLE({}): {:?}", count, ans);
                for i in ans.iter_mut() {
                    *i *= -1;
                }
                // Or you can build a new clause which literals are flipped.
                // let ans: Vec<i32> = ans.iter().map(|i| -i).collect::<Vec<i32>>();
                match solver.add_clause(ans) {
                    Err(SolverError::Inconsistent) => {
                        println!("c no answer due to level zero conflict");
                        break;
                    }
                    Err(e) => {
                        println!("s UNKNOWN; {:?}", e);
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

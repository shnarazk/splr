use std::{env::args, path::Path};
/// All solutions solver implementation based on feature 'incremental solver'
/// But the main purpose is to check the correctness of the implementaion of
/// feature 'incremental solver'.
///
/// To run me:
///```ignore
/// cargo run --features incremental_solver --example all-solutions -- a.cnf
///```

fn main() {
    let cnf_file: String = args().nth(1).expect("takes an arg");
    run(Path::new(&cnf_file));
}

#[cfg(not(feature = "incremental_solver"))]
fn run(_cnf_file: &Path) -> Vec<Vec<i32>> {
    panic!(
        "Pleane run as: cargo run --features incremental_solver --example all-solutions -- a.cnf"
    );
}

#[cfg(feature = "incremental_solver")]
fn run(cnf_file: &Path) -> Vec<Vec<i32>> {
    use splr::cnf::*;
    use splr::*;
    #[cfg(feature = "clause_elimination")]
    {
        panic?("You can't build incremental_solver with feature clause_elimination.")
    }
    let mut solutions = Vec::new();
    let name = cnf_file.file_stem().expect("It seems a strange filename");
    let mut cnf = match CNF::load(cnf_file) {
        Ok(c) => c,
        Err(CNFOperationError::AddingEmptyClause) => {
            return Vec::new();
        }
        Err(e) => {
            panic!("{e:?}");
        }
    };
    println!("{cnf}");
    let mut solver = Solver::try_from(cnf_file).expect("panic");
    let mut count = 0;
    for res in solver.iter() {
        count += 1;
        if res.is_empty() {
            // Is this possible? Yes, an empty form has the solution which contains no literal.
            return vec![vec![]];
        }
        let refuter: Vec<i32> = res.iter().map(|l| -l).collect::<Vec<_>>();
        solutions.push(res);
        cnf.add_clause(refuter).expect("An internal error");
        let dump_name = format!("{}-refuting-{count}.cnf", name.to_string_lossy());
        let dump = Path::new(&dump_name);
        cnf.save(dump).expect("???");
        println!("s SATISFIABLE({count}) => {dump_name}");
    }
    let dump_name = format!("{}-refuting-all{count}.cnf", name.to_string_lossy());
    let dump = Path::new(&dump_name);
    cnf.save(dump).expect("???");
    println!("#solution: {count} => {dump_name}");
    solutions
}

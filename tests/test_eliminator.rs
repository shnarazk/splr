// cargo test -- --nocapture
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
extern crate splr;
use splr::clause::*;
use splr::clause_manage::*;
use splr::solver::*;
use splr::solver::SatSolver;
use splr::types::*;

macro_rules! i2l {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>(),
        }
    };
}

// #[test]
fn check_occurs() {
    let cfg: SolverConfiguration = Default::default();
    let cnf: CNFDescription = CNFDescription {
        num_of_variables: 10,
        num_of_clauses: 10,
        pathname: "".to_string(),
    };
    let mut s = Solver::new(cfg, &cnf);

    let c1 = mk_c(1, vec![1, 2, 3]);
    let c2 = mk_c(2, vec![-2, 3, 4]);
    let c3 = mk_c(3, vec![-2, -3]);
    let c4 = mk_c(4, vec![1, 2, -3, 9]);
    {
        let vec = [&c2, &c3]; // [&c1, &c2, &c3, &c4];
        for x in &vec {
            for y in &vec {
                println!(
                    "{}\tsubsumes\t{}\t=>\t{:?}",
                    x,
                    y,
                    x.subsumes(&y).map(|l| l.int())
                );
            }
        }
    }
    // s.attach_clause(c1);
    s.add_clause(&mut i2l![-2, 3, 4]);
    s.add_clause(&mut i2l![-2, -3]);
    // s.attach_clause(c4);
    // s.vars.dump("##added");
    s.eliminator.dump("##added");
    s.eliminate();
    // s.vars.dump("##eliminated");
    s.eliminator.dump("##eliminated");
    println!("::done");
}

fn mk_c(i: usize, v: Vec<i32>) -> Clause {
    let mut vec = v.iter().map(|i| int2lit(*i)).collect::<Vec<Lit>>();
    let mut c = Clause::new(ClauseKind::Permanent, false, 0, &mut vec, false);
    c.index = i;
    c
}

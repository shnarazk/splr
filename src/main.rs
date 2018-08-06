#![allow(dead_code)]
#![allow(unused_imports)]

extern crate splr;
use splr::clause::*;
use splr::search::*;
use splr::solver::*;
use splr::types::*;

fn main() {
    println!("Hello, world!");
    let cnf = CNFDescription {
        num_of_variables: 8,
        num_of_clauses: 10,
        pathname: "".to_string(),
    };
    let mut s: Solver = Solver::new(DEFAULT_CONFIGURATION, &cnf);
    let x: Lit = int2lit(4);
    let c1 = Clause::new(vec![int2lit(1), int2lit(2), int2lit(3)]);
    let mut c2 = Clause::new(vec![int2lit(-1), int2lit(4)]);
    let mut e = Ema::new(1000);
    for _ in 1..20 {
        e.update(0.2);
    }
    c2.activity = e.get();
    println!("# Literal: L{} -> I{}", x, x.int());
    println!(
        "# Clause: {}, {:?}, {}",
        c1,
        [c1 == c1, c2 == c2, c1 == c2],
        c2.activity
    );
    s.inject(false, c1);
    s.inject(true, c2);
    println!("# Solver: {:?}", s.watches);
    s.solve();
    println!("nclauses = {}", s.num_clauses());
    s.learnts.pop();
    println!("# End of program");
}

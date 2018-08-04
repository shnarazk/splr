#![allow(dead_code)]
#![allow(unused_imports)]

extern crate splr;
use splr::clause::*;
use splr::search::*;
use splr::solver::*;
use splr::types::*;

fn main() {
    let mut s: Solver = Solver::new(&DEFAULT_CONFIGURATION);
    let x: Lit = int2lit(4);
    let null: Clause = Clause::null();
    let mut c2 = Clause::new(vec![int2lit(-1), int2lit(4)]);
    let mut e = Ema::new(1000);
    for _ in 1..20 {
        e.update(0.2);
    }
    c2.activity = e.get();
    println!(
        "Hello, world! L{} -> I{}, {}, {:?}, {}",
        x,
        lit2int(x),
        null,
        [null == null, c2 == c2, null == c2],
        c2.activity
    );
    s.inject(c2);
    s.solve();
    println!("nclauses = {}", s.clauses.clauses.len())
}

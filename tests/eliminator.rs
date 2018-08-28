// cargo test -- --nocapture
extern crate splr;
use splr::types::*;
use splr::clause::*;
use splr::clause_manage::*;
use splr::solver::*;

#[test]
fn check_occurs() {
    let cfg: SolverConfiguration = Default::default();
    let cnf: CNFDescription = CNFDescription {
        num_of_variables: 10,
        num_of_clauses: 10,
        pathname: "".to_string() };
    let mut s = Solver::new(cfg, &cnf);
    let v = vec![1,2,3];
    s.add_clause(v);
    // s.dump("add");
    let c1 = mkC(1, vec![1,2,3]);
    let c2 = mkC(2, vec![1,-2,4]);
    let c3 = mkC(2, vec![1,-2]);
    let vec = &[&c1, &c2, &c3];
    for x in vec {
        for y in vec {
    println!("{}\tsubsumes\t{}\t=>\t{:?}", x, y, x.subsumes(&y).map(|l| l.int()));
        }
    }
    println!("::done");
}


fn mkC(i: usize, v: Vec<i32>) -> Clause {
    let vec = v.iter().map(|i| int2lit(*i)).collect::<Vec<Lit>>();
    let mut c = Clause::new(ClauseKind::Permanent, false, 0, vec);
    c.index = i;
    c
}

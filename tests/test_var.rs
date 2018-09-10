#![allow(dead_code)]
#![allow(unused_macros)]
#![allow(unused_imports)]
extern crate splr;
use splr::clause::*;
use splr::clause_manage::ClauseManagement;
use splr::solver::*;
use splr::types::*;
use splr::var::VarOrdering;

macro_rules! mkc {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => Clause::new(ClauseKind::Permanent, false, v.len(), v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>()),
        }
    };
}

macro_rules! mkb {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => { Clause::new(ClauseKind::Binclause, false, 2,  v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>()) }
        }
    };
}

macro_rules! mkl {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => { Clause::new(ClauseKind::Removable, true, v.len(),  v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>()) }
        }
    };
}


trait TestingSolver {
    fn show_heap(&self) -> ();
}

impl TestingSolver for Solver {
    fn show_heap(&self) -> () {
        let t = self.var_order.len();
        for (i, x) in self.var_order.heap.iter().enumerate() {
            if i <= t {
                println!("#{} {:#} {}", i, x, self.vars[*x as usize].activity);
            } else {
                println!(" {} {:#} {}", i, x, self.vars[*x as usize].activity);
            }
        }
    }
}

#[test]
fn var_order() -> () {
    let mut s = setup();
    s.vars[1].activity = 3.0;
    s.vars[2].activity = 7.0;
    s.vars[3].activity = 10.0;
    s.vars[4].activity = 1.0;
    s.vars[5].activity = 2.0;
    s.vars[6].activity = 5.0;
    s.vars[7].activity = 6.0;
    s.vars[8].activity = 3.0;
    s.var_order.insert(&s.vars, 1);
    s.show_heap();
    println!("remove top {}", s.var_order.root(&s.vars));
    s.show_heap();
    println!("remove top {}", s.var_order.root(&s.vars));
    s.show_heap();
    println!("insert 1");
    s.var_order.insert(&s.vars, 1);
    s.show_heap();
    println!("insert 3");
    s.var_order.insert(&s.vars, 3);
    s.show_heap();
}

fn setup() -> Solver {
    let cnf = CNFDescription {
        num_of_variables: 8,
        num_of_clauses: 5,
        pathname: "".to_string(),
    };
    let mut s = Solver::new(Default::default(), &cnf);
    s.eliminator.use_elim = false;
    s.attach_clause(mkl![1, 2, -3]);     // #1
    s.attach_clause(mkl![1, -2, 3]);     // #2
    s.attach_clause(mkl![-1, 2, 3, 4]);  // #3
    s.attach_clause(mkl![1, -2, 3, 4]);  // #4
    s.attach_clause(mkl![1, 2, -3, 4]);  // #5
    s.attach_clause(mkl![1, 2, 3, -4]);  // #6
    s.attach_clause(mkl![-1, 2, 3, -4]); // #7
    s.attach_clause(mkl![-1, -2, -3]);   // #8
    s
}


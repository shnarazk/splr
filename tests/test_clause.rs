#![allow(unused_macros)]
#![allow(dead_code)]
extern crate splr;
use splr::clause::*;
use splr::solver::*;
use splr::types::*;

macro_rules! i2l {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>(),
        }
    };
}

macro_rules! mkc {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => Clause::new(ClauseKind::Permanent, false, v.len(), &v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>(), false),
        }
    };
}

macro_rules! mkb {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => Clause::new(ClauseKind::Binclause, false, 2,  &v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>(), false),
        }
    };
}

macro_rules! mkl {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => Clause::new(ClauseKind::Removable, true, v.len(), &v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>(), false),
        }
    };
}

trait TestingSolver {
    fn show_clauses(&self) -> ();
}

trait TestingClause {
    fn activity(self, a: f64) -> Self;
    fn rank(self, a: usize) -> Self;
    fn dump(&self) -> String;
}

impl TestingClause for Clause {
    fn activity(mut self, a: f64) -> Clause {
        self.activity = a;
        self
    }
    fn rank(mut self, r: usize) -> Clause {
        self.rank = r;
        self
    }
    fn dump(&self) -> String {
        format!("C{} rank:{}, activity: {}, lit:{:?}{:?}",
                self.index,
                self.rank,
                self.activity,
                self.lit,
                self.lits,
                )
    }
}

impl TestingSolver for Solver {
    fn show_clauses(&self) -> () {
        let target = &self.cp[ClauseKind::Removable as usize];
        for (i, c) in target.clauses.iter().enumerate() {
            println!("#{} {:#}", i, c);
        }
        // println!("permutation len: {}, clauses len: {}", &target.permutation.len(), target.clauses.len());
        // println!("permutation table: {:?}", &target.permutation[1..]);
        // for i in &target.permutation[1..] {
        //    println!("@{} {:#}", i, target.clauses[*i]);
       // }
    }
}

// #[test]
fn clause_equality() -> () {
    let c1 = mkc![1, 2, 3];
    let mut c2 = mkb![-1, 4];
    c2.index = 2;
    c2.activity = 2.4;
    assert_eq!(c1, c1);
    assert_eq!(c1 == c1, true);
    assert_ne!(c1, c2);
    assert_eq!(c2.activity, 2.4);
}

// #[test]
fn clause_iterator() -> () {
    let c1 = mkc![1, 2, 3];
    let mut total = 0;
    for i in &c1 {
        total += i.int();
    }
    assert_eq!(total, 6);
    let mut iter = c1.into_iter();
    assert_eq!(iter.next(), Some(int2lit(1)));
    assert_eq!(iter.next(), Some(int2lit(2)));
    assert_eq!(iter.next(), Some(int2lit(3)));
    assert_eq!(iter.next(), None);
}

#[test]
fn clause_sort() -> () {
    println!("- first senario");
    let mut s = setup();
    assert_eq!(s.ok, true);
    // println!("Clause permutaton: {:?}", &s.cp[ClauseKind::Removable as usize].permutation);
    {
        let ClausePack {
            ref clauses,
            ..
        } = &mut s.cp[ClauseKind::Removable as usize];
        // println!("Before sort clauses: {:?}", &permutation[1..]);
        // permutation[1..].sort_by(|&a, &b| clauses[a].cmp(&clauses[b]));
        // println!("Sort clauses: {:?}", &permutation[1..]);
        // for i in &permutation[1..] {
        //     println!("#{} {:#}", i, &clauses[*i]);
        // }
        //for i in 0..permutation.len() {
        //    permutation[i] = i;
        //}
    }
    s.show_clauses();
    s.cm.reduce(&mut s.cp[0]);
    s.show_clauses();

    s.cm.simplify(&mut s.cp, &s.assign);
    s.show_clauses();

    println!("- another senario");
    let mut s = setup();
    println!(" - initial state");
    s.show_clauses();

    s.cm.reduce(&mut s.cp[0]);
    s.cm.simplify(&mut s.cp, &s.assign);
    println!(" - 1st shrink");
    s.show_clauses();

    s.cm.reduce(&mut s.cp[0]);
    s.cm.simplify(&mut s.cp, &s.assign);
    println!(" - 2nd shrink");
    s.show_clauses();

    s.cm.reduce(&mut s.cp[0]);
    s.cm.simplify(&mut s.cp, &s.assign);
    println!(" - 3rd shrink");
    s.show_clauses();
}

fn setup() -> Solver {
    let cnf = CNFDescription {
        num_of_variables: 4,
        num_of_clauses: 5,
        pathname: "".to_string(),
    };
    let mut s = Solver::new(Default::default(), &cnf);
    s.eliminator.use_elim = false;
    s.add_learnt(&mut i2l![1, 2, -3]);             // #1
    s.add_learnt(&mut i2l![1, 2, -3]);             // #1
    s.add_learnt(&mut i2l![1, 2, -3]);             // #1
    s.add_learnt(&mut i2l![1, 2, -3]);             // #1
    s.add_learnt(&mut i2l![1, 2, -3]);             // #1
    s.add_learnt(&mut i2l![1, 2, -3]);             // #1
    s.add_learnt(&mut i2l![1, 2, -3]);             // #1
//    s.add_clause(&mut mkl![1, -2, 3].activity(4.0).rank(3));     // #2
//    s.add_clause(&mut mkl![-1, 2, 3, 4].activity(5.0));          // #3
//    s.add_clause(&mut mkl![1, -2, 3, 4].activity(2.0).rank(2));  // #4
//    s.add_clause(&mut mkl![1, 2, -3, 4].activity(1.0).rank(2));  // #5
//    s.add_clause(&mut mkl![1, 2, 3, -4].activity(1.0).rank(4));  // #6
//    s.add_clause(&mut mkl![-1, 2, 3, -4].activity(3.0).rank(2)); // #7
//    s.add_clause(&mut mkl![-1, -2, -3].activity(3.0).rank(3));   // #8
    s
}

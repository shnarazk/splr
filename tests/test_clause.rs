#![allow(dead_code)]
extern crate splr;
use splr::clause::*;
use splr::solver::*;
use splr::types::*;

macro_rules! mkc {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => Clause::new(ClauseKind::Permanent, false, v.len(), &v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>()),
        }
    };
}

macro_rules! mkb {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => { Clause::new(ClauseKind::Binclause, false, 2,  &v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>()) }
        }
    };
}

macro_rules! mkl {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => { Clause::new(ClauseKind::Removable, true, v.len(),  &v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>()) }
        }
    };
}

trait Testing {
    fn activity(self, a: f64) -> Self;
    fn rank(self, a: usize) -> Self;
    fn dump(&self) -> String;
}

impl Testing for Clause {
    fn activity(mut self, a: f64) -> Clause {
        self.activity = a;
        self
    }
    fn rank(mut self, r: usize) -> Clause {
        self.rank = r;
        self
    }
    fn dump(&self) -> String {
        format!(
            "C{} rank:{}, activity: {}, lit:{:?}{:?}",
            self.index, self.rank, self.activity, self.lit, self.lits,
        )
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
    let mut s = setup();
    assert_eq!(s.ok, true);
    println!(
        "Clause permutaton: {:?}",
        &s.cp[ClauseKind::Removable as usize].permutation
    );
    {
        let ClausePack {
            ref clauses,
            ref mut permutation,
            ..
        } = &mut s.cp[ClauseKind::Removable as usize];
        println!("Before sort clauses: {:?}", &permutation[1..]);
        permutation[1..].sort_by(|&a, &b| clauses[a].cmp(&clauses[b]));
        println!("Sort clauses: {:?}", &permutation[1..]);
        for i in &permutation[1..] {
            println!("#{} {:#}", i, &clauses[*i]);
        }
        for i in 0..permutation.len() {
            permutation[i] = i;
        }
    }
    s.reduce();
    println!(
        "# reduce_watchers: {:?}",
        &s.cp[ClauseKind::Removable as usize].permutation[1..]
    );
    for (i, c) in s.cp[ClauseKind::Removable as usize]
        .clauses
        .iter()
        .enumerate()
    {
        println!("#{} {:#}", i, c);
    }
    for i in &s.cp[ClauseKind::Removable as usize].permutation[1..] {
        println!(
            "@{} {:#}",
            i,
            &s.cp[ClauseKind::Removable as usize].clauses
                [s.cp[ClauseKind::Removable as usize].permutation[*i]]
        );
    }
    s.simplify();
    println!(
        "# simplify_database: {:?}",
        &s.cp[ClauseKind::Removable as usize].permutation[1..]
    );
    for (i, c) in s.cp[ClauseKind::Removable as usize]
        .clauses
        .iter()
        .enumerate()
    {
        println!("#{} {:#}", i, c);
    }
    for i in &s.cp[ClauseKind::Removable as usize].permutation[1..] {
        println!(
            "@{} {:#}",
            i,
            &s.cp[ClauseKind::Removable as usize].clauses
                [s.cp[ClauseKind::Removable as usize].permutation[*i]]
        );
    }
}

fn setup() -> Solver {
    let cnf = CNFDescription {
        num_of_variables: 4,
        num_of_clauses: 5,
        pathname: "".to_string(),
    };
    let mut s = Solver::new(Default::default(), &cnf);
    s.eliminator.use_elim = false;
    s.attach_clause(mkl![1, 2, -3].activity(1.0));
    s.attach_clause(mkl![1, -2, 3].activity(4.0).rank(3));
    s.attach_clause(mkl![-1, 2, 3, 4].activity(5.0));
    s.attach_clause(mkl![-1, 2, 3, 4].activity(2.0).rank(2));
    s.attach_clause(mkl![-1, 2, 3, 4].activity(1.0).rank(2));
    s.attach_clause(mkl![-1, 2, -3, 4].activity(1.0).rank(4));
    s.attach_clause(mkl![1, 2, -3, -4].activity(3.0).rank(2));
    s
}

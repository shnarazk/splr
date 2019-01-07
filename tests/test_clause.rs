#![allow(dead_code)]
use splr::clause::{ClauseHead, ClauseKind};
use splr::solver::Solver;
use splr::traits::*;
use splr::types::*;

macro_rules! mkv {
    ($($x:expr),*) => {
        match &[$($x),*] {
            v => v.iter().map(|x| int2lit(*x)).collect::<Vec<Lit>>(),
        }
    };
}

trait Testing {
    fn activity(&mut self, a: f64) -> &mut Self;
    fn rank(&mut self, a: usize) -> &mut Self;
}

impl Testing for ClauseHead {
    fn activity(&mut self, a: f64) -> &mut ClauseHead {
        self.activity = a;
        self
    }
    fn rank(&mut self, r: usize) -> &mut ClauseHead {
        self.rank = r;
        self
    }
}

// // #[test]
// fn clause_equality() -> () {
//     let c1 = mkv![1, 2, 3];
//     let mut c2 = mkv![-1, 4];
//     c2.index = 2;
//     c2.activity = 2.4;
//     assert_eq!(c1, c1);
//     assert_eq!(c1 == c1, true);
//     assert_ne!(c1, c2);
//     assert_eq!(c2.activity, 2.4);
// }
//
// // #[test]
// fn clause_iterator() -> () {
//     let c1 = mkc![1, 2, 3];
//     let mut total = 0;
//     for i in &c1 {
//         total += i.int();
//     }
//     assert_eq!(total, 6);
//     let mut iter = c1.into_iter();
//     assert_eq!(iter.next(), Some(int2lit(1)));
//     assert_eq!(iter.next(), Some(int2lit(2)));
//     assert_eq!(iter.next(), Some(int2lit(3)));
//     assert_eq!(iter.next(), None);
// }

#[test]
fn clause_sort() -> () {
    let s = setup();
    assert_eq!(s.state.ok, true);
}

fn setup() -> Solver {
    let cnf = CNFDescription {
        num_of_variables: 5,
        num_of_clauses: 6,
        pathname: "".to_string(),
    };
    let mut s = Solver::new(Default::default(), &cnf);
    attach_clause(&mut s, &mkv![1, 2, -3]).activity(1.0);
    attach_clause(&mut s, &mkv![1, -2, 3]).activity(4.0).rank(3);
    attach_clause(&mut s, &mkv![-1, 2, 3, 4]).activity(5.0);
    attach_clause(&mut s, &mkv![-1, 2, 3, 5])
        .activity(2.0)
        .rank(2);
    attach_clause(&mut s, &mkv![-1, 2, -3, -4])
        .activity(1.0)
        .rank(2);
    attach_clause(&mut s, &mkv![-1, 2, -3, 4])
        .activity(1.0)
        .rank(4);
    attach_clause(&mut s, &mkv![1, 2, -3, -4])
        .activity(3.0)
        .rank(2);
    s
}

fn attach_clause<'a>(s: &'a mut Solver, vec: &[Lit]) -> &'a mut ClauseHead {
    let cid = s.cps[ClauseKind::Permanent as usize].new_clause(vec, vec.len());
    &mut s.cps[ClauseKind::Permanent as usize].head[cid.to_index()]
}

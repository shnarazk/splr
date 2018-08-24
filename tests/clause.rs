extern crate splr;
use splr::types::*;
use splr::clause::*;

#[test]
fn clause_equality() -> () {
    let c1 = splr::clause::Clause::new(ClauseKind::Permanent, false, 3, vec![int2lit(1), int2lit(2), int2lit(3)]);
    let mut c2 = splr::clause::Clause::new(ClauseKind::Permanent, true, 2, vec![int2lit(-1), int2lit(4)]);
    c2.index = 2;
    c2.activity = 2.4;
    assert_eq!(c1, c1);
    assert_eq!(c1 == c1, true);
    assert_ne!(c1, c2);
    assert_eq!(c2.activity, 2.4);
}

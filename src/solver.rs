use clause::*;
use types::*;

pub struct Solver {
    null_clause: Clause,
    clauses: Vec<BoxClause>,
    learnts: Vec<BoxClause>,
    watches: Vec<ClauseExtManager>,
    assigns: Vec<i8>,
    phases: Vec<i8>,
}

impl Solver {
    fn new() -> Solver {
        Solver {
            null_clause: Clause::null(),
            clauses: vec![Box::new(Clause::new(vec![]))],
            learnts: vec![Box::new(Clause::new(vec![]))],
            watches: vec![],
            assigns: vec![0; 10],
            phases: vec![0; 10],
        }
    }
}

#![allow(dead_code)]
#![allow(unused_imports)]
use clause::*;
use types::*;

pub struct Solver {
    null_clause: Clause,
    clauses: ClauseManager,
    learnts: ClauseManager,
    watches: Vec<ClauseManager>,
    assigns: Vec<i8>,
    phases: Vec<i8>,
}

impl Solver {
    fn new() -> Solver {
        Solver {
            null_clause: Clause::null(),
            clauses: ClauseManager::new(),
            learnts: ClauseManager::new(),
            watches: vec![],
            assigns: vec![0; 10],
            phases: vec![0; 10],
        }
    }
}

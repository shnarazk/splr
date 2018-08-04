#![allow(dead_code)]
#![allow(unused_imports)]
use clause::*;
use types::*;

/// In splr, `watchers` is reseted at the beginning of simplify phase.
/// It's just a mutable vector referring immutable Clause.
/// Because, during propagate, all clauses are immutable.
pub struct Watcher<'a> {
    other: Lit,
    by: &'a Clause,
}

pub struct Solver<'a> {
    null_clause: Clause,
    clauses: ClauseManager,
    learnts: ClauseManager,
    watches: Vec<Vec<Watcher<'a>>>,
    assigns: Vec<LBool>,
    phases: Vec<i8>,
    config: &'a SolverConfiguration,
}

impl<'a> Solver<'a> {
    fn new(cfg: &'a SolverConfiguration) -> Solver<'a> {
        Solver {
            null_clause: Clause::null(),
            clauses: ClauseManager::new(),
            learnts: ClauseManager::new(),
            watches: vec![],
            assigns: vec![0; 10],
            phases: vec![0; 10],
            config: cfg,
        }
    }
    fn value_of(&self, l: Lit) -> LBool {
        let x = self.assigns[lit2var(l) as usize];
        if x == BOTTOM {
            BOTTOM
        } else if positive_lit(l) {
            x
        } else {
            negate(x)
        }
    }
    fn satisfies(&self, c: Clause) -> bool {
        for l in c.lits {
            if self.value_of(l) == LTRUE {
                return true;
            }
        }
        return false;
    }
}

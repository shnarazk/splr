#![allow(dead_code)]
#![allow(unused_imports)]
use clause::*;
use types::*;

/// In splr, `watchers` is reseted at the beginning of simplify phase.
/// It's just a mutable vector referring immutable Clause.
/// Because, during propagate, all clauses are immutable.
pub struct Watcher<'a> {
    pub other: Lit,
    pub by: &'a Clause,
}

/// WatcherVec
pub type WatcherVec<'a> = Vec<Vec<Watcher<'a>>>;

pub fn new_watcher_vec<'a>(n: u32) -> WatcherVec<'a> {
    let mut vec = Vec::new();
    for _i in 0..n {
        vec.push(Vec::new());
    }
    vec
}

pub struct Solver<'a> {
    pub null_clause: Clause,
    pub clauses: ClauseManager,
    pub learnts: ClauseManager,
    pub watches: WatcherVec<'a>,
    pub assigns: Vec<LBool>,
    pub phases: Vec<i8>,
    pub config: &'a SolverConfiguration,
}

impl<'a> Solver<'a> {
    pub fn new(cfg: &'a SolverConfiguration, cnf: &CNFDescription) -> Solver<'a> {
        Solver {
            null_clause: Clause::null(),
            clauses: ClauseManager::new(),
            learnts: ClauseManager::new(),
            watches: new_watcher_vec(cnf.num_of_variables * 2),
            assigns: vec![0; 10],
            phases: vec![0; 10],
            config: cfg,
        }
    }
    pub fn value_of(&self, l: Lit) -> LBool {
        let x = self.assigns[lit2var(l) as usize];
        if x == BOTTOM {
            BOTTOM
        } else if positive_lit(l) {
            x
        } else {
            negate(x)
        }
    }
    pub fn satisfies(&self, c: Clause) -> bool {
        for l in c.lits {
            if self.value_of(l) == LTRUE {
                return true;
            }
        }
        return false;
    }
    pub fn inject(&mut self, c: Clause) -> () {
        self.clauses.push((0, c));
    }
}

pub fn cancel_until(_s: &mut Solver, _l: Lit) -> () {}

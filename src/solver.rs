use clause::ClauseManagement;
use clause::*;
use restart::Restart;
use std::cmp::max;
use std::fs;
use std::io::{BufRead, BufReader};
use types::Dump;
use types::*;
use var::*;
use var_manage::VarSelect;

pub trait SatSolver {
    fn solve(&mut self) -> SolverResult;
    fn build(path: &str) -> (Solver, CNFDescription);
}

pub trait CDCL {
    /// returns `true` for SAT, `false` for UNSAT.
    fn search(&mut self) -> bool;
    fn propagate(&mut self) -> ClauseId;
    fn cancel_until(&mut self, lv: usize) -> ();
    fn enqueue(&mut self, l: Lit, cid: ClauseId) -> bool;
    fn analyze(&mut self, confl: ClauseId) -> usize;
    fn analyze_final(&mut self, ci: ClauseId, skip_first: bool) -> ();
}

const CO_LBD_BOUND: usize = 4;

/// normal results returned by Solver
#[derive(Debug)]
pub enum Certificate {
    SAT(Vec<i32>),
    UNSAT(Vec<i32>), // FIXME: replace with DRAT
}

/// abnormal termination flags
#[derive(Debug, Eq, PartialEq)]
pub enum SolverException {
    StateUNSAT = 0,
    StateSAT,             // 1
    OutOfMemory,          // 2
    TimeOut,              // 3
    InternalInconsistent, // 4
    UndescribedError,     // 5
}

/// The type that `Solver` returns
/// This captures the following three cases:
/// * solved with a satisfiable assigment,
/// * proved that it's an unsatisfiable problem, and
/// * aborted due to Mios specification or an internal error
pub type SolverResult = Result<Certificate, SolverException>;

/// stat index
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum Stat {
    Conflict = 0,       // the number of backjump
    Decision,           // the number of decision
    Restart,            // the number of restart
    NoDecisionConflict, // the number of 'no decision conflict'
    BlockRestart,       // the number of blacking start
    Propagation,        // the number of propagation
    Reduction,          // the number of reduction
    Simplification,     // the number of simplification
    Clause,             // the number of 'alive' given clauses
    Learnt,             // the number of 'alive' learnt clauses
    Variable,           // the number of 'alive' variables
    GroundVar,          // the number os assined variables at level 0
    Assign,             // the number of assigned variables
    EndOfStatIndex,     // Don't use this dummy.
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SearchStrategy {
    Generic,
    ChanSeok,
    HighSuccesive,
    LowSuccesive,
    ManyGlues,
}

/// is the collection of all variables.
#[derive(Debug)]
pub struct Solver {
    /// Configuration
    pub config: SolverConfiguration,
    pub num_vars: usize,
    pub cla_inc: f64,
    pub var_inc: f64,
    pub root_level: usize,
    pub strategy: Option<SearchStrategy>,
    /// Variable Assignment Management
    pub vars: Vec<Var>,
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
    /// Variable Order
    pub var_order: VarIdHeap,
    /// Clause Database Management
    pub cp: [ClausePack; 3],
    pub first_reduction: usize,
    pub next_reduction: usize,
    pub cur_restart: usize,
    pub num_solved_vars: usize,
    /// Variable Elimination
    pub eliminator: Eliminator,
    /// Working memory
    pub ok: bool,
    pub model: Vec<Lbool>,
    pub conflicts: Vec<Lit>,
    pub stats: Vec<i64>,
    pub an_seen: Vec<Lit>,
    pub an_to_clear: Vec<Lit>,
    pub an_stack: Vec<Lit>,
    pub an_last_dl: Vec<Lit>,
    pub an_learnt_lits: Vec<Lit>,
    pub an_level_map: Vec<usize>,
    pub an_level_map_key: usize,
    pub mi_var_map: Vec<usize>,
    pub lbd_seen: Vec<u64>,
    /// restart heuristics
    pub ema_asg: Ema2,
    pub ema_lbd: Ema2,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub next_restart: u64,
    pub restart_exp: f64,
    pub rbias: Ema,
}

impl Solver {
    pub fn new(cfg: SolverConfiguration, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let (_fe, se) = cfg.ema_coeffs;
        let re = cfg.restart_expansion;
        let cdr = cfg.clause_decay_rate;
        let vdr = cfg.variable_decay_rate;
        let use_sve = cfg.use_sve;
        Solver {
            config: cfg,
            num_vars: nv,
            cla_inc: cdr,
            var_inc: vdr,
            root_level: 0,
            strategy: None,
            vars: Var::new_vars(nv),
            trail: Vec::with_capacity(nv),
            trail_lim: Vec::new(),
            q_head: 0,
            var_order: VarIdHeap::new(VarOrder::ByActivity, nv, nv),
            cp: [
                ClausePack::build(ClauseKind::Removable, nv, nc),
                ClausePack::build(ClauseKind::Permanent, nv, 256),
                ClausePack::build(ClauseKind::Binclause, nv, 256),
            ],
            first_reduction: 1000,
            next_reduction: 1000,
            cur_restart: 1,
            num_solved_vars: 0,
            eliminator: Eliminator::new(use_sve, nv),
            ok: true,
            model: vec![BOTTOM; nv + 1],
            conflicts: vec![],
            stats: vec![0; Stat::EndOfStatIndex as usize],
            an_seen: vec![0; nv + 1],
            an_to_clear: vec![0; nv + 1],
            an_stack: vec![],
            an_last_dl: vec![],
            an_learnt_lits: vec![],
            an_level_map: vec![0; nv + 1],
            an_level_map_key: 1,
            mi_var_map: vec![0; nv + 1],
            lbd_seen: vec![0; nv + 1],
            ema_asg: Ema2::new(4.0, 8192.0),  // for blocking
            ema_lbd: Ema2::new(64.0, 8192.0), // for forcing
            b_lvl: Ema::new(se),
            c_lvl: Ema::new(se),
            next_restart: 100,
            restart_exp: re,
            rbias: Ema::new(se),
        }
    }
    // print a progress report
    pub fn progress(&self, mes: &str) -> () {
        let nv = self.vars.len() - 1;
        let k = if self.trail_lim.is_empty() {
            self.trail.len()
        } else {
            self.trail_lim[0]
        };
        let sum = k + self.eliminator.eliminated_vars;
        let learnts = &self.cp[ClauseKind::Removable as usize];
        let deads = learnts.count(GARBAGE_LIT, 0) + learnts.count(RECYCLE_LIT, 0);
        let cnt = learnts
            .clauses
            .iter()
            .filter(|c| c.index != 0 && !c.get_flag(ClauseFlag::Dead) && c.rank <= 2)
            .count();
        if mes == "" {
            println!("#init, DB, #Remov, #good,#junk,  #Perm,#Binary, PROG,#solv,#elim, rate%, RES,block,force, asgn/,  lbd/, STAT,   lbd, b lvl, c lvl");
        } else {
            println!(
                "#{}, DB,{:>7},{:>6},{:>5},{:>7},{:>7}, PROG,{:>5},{:>5},{:>6.3}, RES,{:>5},{:>5}, {:>5.2},{:>6.2}, STAT,{:>6.2},{:>6.2},{:>6.2}",
                mes,
                learnts.clauses.len() - 1 -deads,
                cnt,
                deads,
                self.cp[ClauseKind::Permanent as usize].clauses.iter().filter(|c| !c.get_flag(ClauseFlag::Dead)).count(),
                self.cp[ClauseKind::Binclause as usize].clauses.iter().filter(|c| !c.get_flag(ClauseFlag::Dead)).count(),
                k,
                self.eliminator.eliminated_vars,
                (sum as f32) / (nv as f32) * 100.0,
                self.stats[Stat::BlockRestart as usize],
                self.stats[Stat::Restart as usize],
                self.ema_asg.get(),
                self.ema_lbd.get(),
                self.ema_lbd.fast,
                self.b_lvl.0,
                self.c_lvl.0,
            );
        }
        // if 10000 < learnts.len() {
        //     for c in &learnts.clauses.iter().filter(|&c| !c.get_flag(ClauseFlag::Dead) && c.rank <= 2).take(4).collect::<Vec<&Clause>>() {
        //         println!("{:?}", *c);
        //         for i in 0..c.len() {
        //             let v = lindex!(*c, i).vi();
        //             println!(" - v{} => {}", v, self.vars[v].level);
        //         }
        //     }
        // }
    }

    pub fn num_assigns(&self) -> usize {
        self.trail.len()
    }

    #[inline]
    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    pub fn attach_clause(&mut self, c: Clause) -> ClauseId {
        if self.eliminator.use_elim {
            for i in 0..c.len() {
                let l = lindex!(c, i);
                self.vars[l.vi()].touched = true;
                self.eliminator.n_touched += 1;
            }
        }
        let cid = self.cp[c.get_kind() as usize].attach(c);
        debug_assert_ne!(cid, 0);
        cid
    }

    pub fn adapt_strategy(&mut self) -> () {
        let mut re_init = false;
        if self.strategy != None {
            return;
        }
        let decpc = self.stats[Stat::Decision as usize] as f64
            / self.stats[Stat::Conflict as usize] as f64;
        if decpc <= 1.2 {
            self.strategy = Some(SearchStrategy::ChanSeok);
            let _glureduce = true;
            self.first_reduction = 2000;
            self.next_reduction = 2000;
            self.cur_restart = ((self.stats[Stat::Conflict as usize] as f64 / self.next_reduction as f64) + 1.0) as usize;
            // TODO incReduceDB = 0;
            println!("# Adjusting for low decision levels.");
            re_init = true;
        } else if self.stats[Stat::NoDecisionConflict as usize] < 30_000 {
            self.strategy = Some(SearchStrategy::Generic);
        } else {
        }
        if self.strategy != None {
            self.ema_asg.reset();
            self.ema_lbd.reset();
            // conflictsRestarts = 0;
            if self.strategy == Some(SearchStrategy::ChanSeok) {
                // TODO
                // move some clauses with good lbd (col_lbd_bound) to Permanent
                // 1. cp[ClausePack::Permanent]attach(clause);
                // 2. clause.set_flag(ClauseFlag::Dead);
                for c in &mut self.cp[ClauseKind::Removable as usize].clauses {
                    if c.rank < CO_LBD_BOUND {
                        // 1. cp[ClausePack::Permanent]attach(clause);
                        // 2. clause.set_flag(ClauseFlag::Dead);
                    }
                }
            }
        }
        if re_init {
            // make all claueses garbage
        }
    }
}

impl SatSolver for Solver {

    fn solve(&mut self) -> SolverResult {
        if !self.ok {
            return Ok(Certificate::UNSAT(Vec::new()));
        }
        // TODO: deal with assumptions
        // s.root_level = 0;
        self.num_solved_vars = self.trail.len();
        // if self.eliminator.use_elim {
        //     // self.eliminate_binclauses();
        //     self.eliminate();
        // }
        self.progress("");
        self.simplify();
        self.stats[Stat::Simplification as usize] += 1;
        match self.search() {
            _ if !self.ok => {
                self.cancel_until(0);
                Err(SolverException::InternalInconsistent)
            }
            true => {
                let mut result = Vec::new();
                for vi in 1..self.num_vars + 1 {
                    match self.vars[vi].assign {
                        LTRUE => result.push(vi as i32),
                        LFALSE => result.push(0 - vi as i32),
                        _ => result.push(0),
                    }
                }
                if self.eliminator.use_elim {
                    self.extend_model(&mut result);
                }
                self.cancel_until(0);
                Ok(Certificate::SAT(result))
            }
            false => {
                self.cancel_until(0);
                let mut v = Vec::new();
                for l in &self.conflicts {
                    v.push(l.int());
                }
                Ok(Certificate::UNSAT(v))
            }
        }
    }

    /// builds and returns a configured solver.
    fn build(path: &str) -> (Solver, CNFDescription) {
        let mut rs = BufReader::new(fs::File::open(path).unwrap());
        let mut buf = String::new();
        let mut nv: usize = 0;
        let mut nc: usize = 0;
        loop {
            buf.clear();
            match rs.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_k) => {
                    let mut iter = buf.split_whitespace();
                    if iter.next() == Some("p") && iter.next() == Some("cnf") {
                        if let Some(v) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                            if let Some(c) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                                nv = v;
                                nc = c;
                                break;
                            }
                        }
                    }
                    continue;
                }
                Err(e) => panic!("{}", e),
            }
        }
        let cnf = CNFDescription {
            num_of_variables: nv,
            num_of_clauses: nc,
            pathname: path.to_string(),
        };
        let mut s: Solver = Solver::new(SolverConfiguration::default(), &cnf);
        loop {
            buf.clear();
            match rs.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_) => {
                    if buf.starts_with('c') {
                        continue;
                    }
                    let mut iter = buf.split_whitespace();
                    let mut v: Vec<Lit> = Vec::new();
                    for s in iter {
                        if let Ok(val) = s.parse::<i32>() {
                            if val == 0 {
                                break;
                            } else {
                                v.push(int2lit(val));
                            }
                        }
                    }
                    if !v.is_empty() && !s.add_clause(&mut v) {
                        s.ok = false;
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        debug_assert_eq!(s.vars.len() - 1, cnf.num_of_variables);
        (s, cnf)
    }
}

impl CDCL for Solver {

    fn propagate(&mut self) -> ClauseId {
        let Solver {
            ref mut vars,
            ref mut cp,
            ref mut trail,
            ref trail_lim,
            ref mut q_head,
            ref mut stats,
            ..
        } = self;
        while *q_head < trail.len() {
            let p: usize = trail[*q_head] as usize;
            let false_lit = (p as Lit).negate();
            *q_head += 1;
            stats[Stat::Propagation as usize] += 1;
            let kinds = [
                ClauseKind::Binclause,
                ClauseKind::Removable,
                ClauseKind::Permanent,
            ];
            let mut ci: ClauseIndex;
            for kind in &kinds {
                unsafe {
                    let clauses = &mut cp[*kind as usize].clauses[..] as *mut [Clause];
                    let watcher = &mut cp[*kind as usize].watcher[..] as *mut [ClauseIndex];
                    ci = (*watcher)[p];
                    let mut tail = &mut (*watcher)[p] as *mut usize;
                    *tail = NULL_CLAUSE;
                    'next_clause: while ci != NULL_CLAUSE {
                        let c = &mut (*clauses)[ci] as *mut Clause;
                        if (*c).lit[0] == false_lit {
                            (*c).lit.swap(0, 1); // now my index is 1, others is 0.
                            (*c).next_watcher.swap(0, 1);
                        }
                        ci = (*c).next_watcher[1];
                        // let next = (*c).next_watcher[1];
                        let other = (*c).lit[0];
                        let other_value = vars.assigned(other);
                        if other_value != LTRUE {
                            for (k, lk) in (*c).lits.iter().enumerate() {
                                // below is equivalent to 'assigned(lk) != LFALSE'
                                if (((lk & 1) as u8) ^ vars[lk.vi()].assign) != 0 {
                                    let alt = &mut (*watcher)[lk.negate() as usize];
                                    (*c).next_watcher[1] = *alt;
                                    *alt = (*c).index;
                                    (*c).lit[1] = *lk;
                                    (*c).lits[k] = false_lit; // WARN: update this lastly (needed by enuremate)
                                    continue 'next_clause;
                                }
                            }
                            if other_value == LFALSE {
                                *tail = (*c).index;
                                *q_head = trail.len();
                                return kind.id_from((*c).index);
                            } else {
                                // uncheck_enqueue(lit, kind.id_from((*c).index));
                                // uenqueue!(vars, trail, trail_lim, lit, kind.id_from((*c).index));
                                let dl = trail_lim.len();
                                let v = &mut vars[other.vi()];
                                v.assign = other.lbool();
                                v.level = dl;
                                v.reason = kind.id_from((*c).index);
                                trail.push(other);
                                (*c).set_flag(ClauseFlag::Locked, true);
                            }
                        }
                        let watch = (*watcher)[p];
                        if watch == 0 {
                            tail = &mut (*c).next_watcher[1];
                        }
                        (*c).next_watcher[1] = watch;
                        (*watcher)[p] = (*c).index;
                    }
                }
            }
        }
        NULL_CLAUSE
    }

    /// main loop
    fn search(&mut self) -> bool {
        let root_lv = self.root_level;
        loop {
            self.stats[Stat::Propagation as usize] += 1;
            let ci = self.propagate();
            if ci == NULL_CLAUSE {
                let na = self.num_assigns();
                if na == self.num_vars {
                    return true;
                }
                self.force_restart();
                if self.decision_level() == 0 && self.num_solved_vars < na {
                    self.simplify();
                    self.num_solved_vars = self.num_assigns();
                    self.rebuild_vh();
                }
                if self.trail.len() <= self.q_head {
                    let vi = self.select_var();
                    debug_assert_ne!(vi, 0);
                    let p = self.vars[vi].phase;
                    self.uncheck_assume(vi.lit(p));
                    self.stats[Stat::Decision as usize] += 1;
                }
            } else {
                self.stats[Stat::Conflict as usize] += 1;
                let dl = self.decision_level();
                if dl == self.root_level {
                    self.analyze_final(ci, false);
                    return false;
                } else {
                    let bl = self.analyze(ci);
                    let nas = self.num_assigns();
                    self.cancel_until(max(bl as usize, root_lv));
                    let lbd;
                    if self.an_learnt_lits.len() == 1 {
                        let l = self.an_learnt_lits[0];
                        println!("unit literal {}", l.int());
                        self.uncheck_enqueue(l, NULL_CLAUSE);
                        lbd = 0;
                    } else {
                        unsafe {
                            let v = &mut self.an_learnt_lits as *mut Vec<Lit>;
                            lbd = self.lbd_vec(&*v);
                            if self.strategy == Some(SearchStrategy::ChanSeok) && lbd <= CO_LBD_BOUND {
                                // TODO
                                self.add_learnt(&mut *v, lbd);
                            } else {
                                self.add_learnt(&mut *v, lbd);
                            }
                        }
                    }
                    if self.stats[Stat::Conflict as usize] == 100_000 {
                        self.cancel_until(0);
                        self.adapt_strategy();
                    } else {
                        self.block_restart(lbd, dl, bl, nas);
                    }
                    // self.decay_var_activity();
                    self.decay_cla_activity();
                    // glucose reduction
                    let conflicts = self.stats[Stat::Conflict as usize] as usize;
                    if self.cur_restart * self.next_reduction <= conflicts {
                        self.cur_restart =
                            ((conflicts as f64) / (self.next_reduction as f64)) as usize + 1;
                        self.reduce();
                    }
                }
                // Since the conflict path pushes a new literal to trail, we don't need to pick up a literal here.
            }
        }
    }

    fn cancel_until(&mut self, lv: usize) -> () {
        if self.decision_level() <= lv {
            return;
        }
        let lim = self.trail_lim[lv];
        for l in &self.trail[lim..] {
            let vi = l.vi();
            {
                let v = &mut self.vars[vi];
                v.phase = v.assign;
                v.assign = BOTTOM;
                if v.reason != NULL_CLAUSE {
                    self.cp[v.reason.to_kind()].clauses[v.reason.to_index()]
                        .set_flag(ClauseFlag::Locked, false);
                }
                v.reason = NULL_CLAUSE;
            }
            self.var_order.insert(&self.vars, vi);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(lv);
        self.q_head = lim;
    }

    fn enqueue(&mut self, l: Lit, cid: ClauseId) -> bool {
        let sig = l.lbool();
        let val = self.vars[l.vi()].assign;
        if val == BOTTOM {
            {
                let dl = self.decision_level();
                let v = &mut self.vars[l.vi()];
                v.assign = sig;
                v.level = dl;
                v.reason = cid;
                mref!(self.cp, cid).set_flag(ClauseFlag::Locked, true);
            }
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }

    fn analyze(&mut self, confl: ClauseId) -> usize {
        self.an_learnt_lits.clear();
        self.an_learnt_lits.push(0);
        let dl = self.decision_level();
        let mut cid: usize = confl;
        let mut p = NULL_LIT;
        let mut ti = self.trail.len() - 1; // trail index
        let mut path_cnt = 0;
        loop {
            unsafe {
                let c = &mut self.cp[cid.to_kind()].clauses[cid.to_index()] as *mut Clause;
                debug_assert_ne!(cid, NULL_CLAUSE);
                let d = (*c).rank;
                if cid.to_kind() == (ClauseKind::Removable as usize) {
                    self.bump_cid(cid);
                    // let nblevels = self.lbd_of(&(*c));
                    // if nblevels + 1 < d {
                    //     debug_assert!(0 < nblevels);
                    //     // (*c).rank = nblevels;
                    //     // if nblevels <= 30 {
                    //     //     (*c).set_flag(ClauseFlag::JustUsed, true);
                    //     // }
                    // }
                }
                // println!("{}を対応", (*c));
                //                'next_literal: for q in &(*c).lits {
                for i in ((p != NULL_LIT) as usize)..(*c).len() {
                    let q = lindex!(*c, i);
                    let vi = q.vi();
                    let lvl = self.vars[vi].level;
                    if self.vars[vi].assign == BOTTOM {
                        panic!(" analyze faced bottom by vi {} in {}", vi, (*c));
                    }
                    debug_assert_ne!(self.vars[vi].assign, BOTTOM);
                    if self.an_seen[vi] == 0 && 0 < lvl {
                        self.bump_vi(vi);
                        self.an_seen[vi] = 1;
                        if dl <= lvl {
                            // println!(
                            //     "{} はレベル{}なのでフラグを立てる",
                            //     q.int(),
                            //     l
                            // );
                            path_cnt += 1;
                            if self.vars[vi].reason != NULL_CLAUSE {
                                self.an_last_dl.push(q);
                            }
                        } else {
                            // println!("{} はレベル{}なので採用", q.int(), l);
                            self.an_learnt_lits.push(q);
                        }
                    } else {
                        // println!("{} はもうフラグが立っているかグラウンドしている{}ので無視", q.int(), l);
                    }
                }
                // set the index of the next literal to ti
                while self.an_seen[self.trail[ti].vi()] == 0 {
                    // println!(
                    //     "{} はフラグが立ってないので飛ばす",
                    //     self.trail[ti].int()
                    // );
                    ti -= 1;
                }
                p = self.trail[ti];
                {
                    let next_vi = p.vi();
                    cid = self.vars[next_vi].reason;
                    // println!("{} にフラグが立っている。この時path数は{}, そのreason {}を探索", next_vi, path_cnt - 1, cid);
                    self.an_seen[next_vi] = 0;
                }
                path_cnt -= 1;
                if path_cnt <= 0 {
                    break;
                }
                ti -= 1;
            }
        }
        self.an_learnt_lits[0] = p.negate();
        // println!(
        //     "最後に{}を採用して{:?}",
        //     p.negate().int(), vec2int(self.an_learnt_lits)
        // );
        // simplify phase
        let n = self.an_learnt_lits.len();
        let l0 = self.an_learnt_lits[0];
        self.an_stack.clear();
        self.an_to_clear.clear();
        self.an_to_clear.push(l0);
        {
            self.an_level_map_key += 1;
            if 10_000_000 < self.an_level_map_key {
                self.an_level_map_key = 1;
            }
            for i in 1..n {
                let l = self.an_learnt_lits[i];
                self.an_to_clear.push(l);
                self.an_level_map[self.vars[l.vi()].level] = self.an_level_map_key;
            }
        }
        // println!("  analyze.loop 4 n = {}", n);
        let mut j = 1;
        for i in 1..n {
            let l = self.an_learnt_lits[i];
            if self.vars[l.vi()].reason == NULL_CLAUSE || !self.analyze_removable(l) {
                self.an_learnt_lits[j] = l;
                j += 1;
            }
        }
        self.an_learnt_lits.truncate(j);
        // glucose heuristics
        let r = self.an_learnt_lits.len();
        for i in 0..self.an_last_dl.len() {
            let vi = self.an_last_dl[i].vi();
            let cid = self.vars[vi].reason;
            let len = self.cp[cid.to_kind()].clauses[cid.to_index()].lits.len();
            if r < len {
                self.bump_vi(vi);
            }
        }
        self.an_last_dl.clear();
        for l in &self.an_to_clear {
            self.an_seen[l.vi()] = 0;
        }
        if self.an_learnt_lits.len() < 30 {
            self.minimize_with_bi_clauses();
        }
        // find correct backtrack level from remaining literals
        let mut level_to_return = 0;
        if self.an_learnt_lits.len() != 1 {
            let mut max_i = 1;
            level_to_return = self.vars[self.an_learnt_lits[max_i].vi()].level;
            for i in 2..self.an_learnt_lits.len() {
                let lv = self.vars[self.an_learnt_lits[i].vi()].level;
                if level_to_return < lv {
                    level_to_return = lv;
                    max_i = i;
                }
            }
            self.an_learnt_lits.swap(1, max_i);
        }
        for l in &self.an_to_clear {
            self.an_seen[l.vi()] = 0;
        }
        level_to_return
    }

    fn analyze_final(&mut self, ci: ClauseId, skip_first: bool) -> () {
        self.conflicts.clear();
        if self.root_level != 0 {
            //for i in &self.clauses.iref(ci).lits[(if skip_first { 1 } else { 0 })..] {
            for i in (if skip_first { 1 } else { 0 })
                ..(self.cp[ci.to_kind()].clauses[ci.to_index()].len())
            {
                let l;
                match i {
                    0 => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lit[0],
                    1 => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lit[1],
                    _ => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lits[i - 2],
                }
                let vi = l.vi();
                if 0 < self.vars[vi].level {
                    self.an_seen[vi] = 1;
                }
            }
            let tl0 = self.trail_lim[0];
            let start = if self.trail_lim.len() <= self.root_level {
                self.trail.len()
            } else {
                self.trail_lim[self.root_level]
            };
            for i in (tl0..start).rev() {
                let l: Lit = self.trail[i];
                let vi = l.vi();
                if self.an_seen[vi] == 1 {
                    if self.vars[vi].reason == NULL_CLAUSE {
                        self.conflicts.push(l.negate());
                    } else {
                        for i in 1..(self.cp[ci.to_kind()].clauses[ci.to_index()].lits.len()) {
                            let l;
                            match i {
                                0 => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lit[1],
                                _ => l = &self.cp[ci.to_kind()].clauses[ci.to_index()].lits[i - 2],
                            }
                            // for l in &self.clauses.iref(ci).lits[1..]
                            let vi = l.vi();
                            if 0 < self.vars[vi].level {
                                self.an_seen[vi] = 1;
                            }
                        }
                    }
                }
                self.an_seen[vi] = 0;
            }
        }
    }
}

impl Solver {
    /// renamed from litRedundant
    fn analyze_removable(&mut self, l: Lit) -> bool {
        self.an_stack.clear();
        self.an_stack.push(l);
        let top = self.an_to_clear.len();
        let key = self.an_level_map_key;
        while let Some(sl) = self.an_stack.pop() {
            // println!("analyze_removable.loop {:?}", self.an_stack);
            let cid = self.vars[sl.vi()].reason;
            let c0;
            let len;
            {
                let c = &self.cp[cid.to_kind()].clauses[cid.to_index()];
                c0 = c.lit[0];
                len = c.lits.len();
            }
            if len == 0 && self.vars.assigned(c0) == LFALSE {
                self.cp[cid.to_kind()].clauses[cid.to_index()]
                    .lit
                    .swap(0, 1);
            }
            for i in 0..self.cp[cid.to_kind()].clauses[cid.to_index()].lits.len() + 1 {
                let q;
                match i {
                    0 => q = self.cp[cid.to_kind()].clauses[cid.to_index()].lit[1],
                    n => q = self.cp[cid.to_kind()].clauses[cid.to_index()].lits[n - 1],
                }
                let vi = q.vi();
                let lv = self.vars[vi].level;
                if self.an_seen[vi] != 1 && lv != 0 {
                    if self.vars[vi].reason != NULL_CLAUSE && self.an_level_map[lv as usize] == key
                    {
                        self.an_seen[vi] = 1;
                        self.an_stack.push(q);
                        self.an_to_clear.push(q);
                    } else {
                        for _ in top..self.an_to_clear.len() {
                            self.an_seen[self.an_to_clear.pop().unwrap().vi()] = 0;
                        }
                        return false;
                    }
                }
            }
        }
        true
    }

    fn minimize_with_bi_clauses(&mut self) -> () {
        let len = self.an_learnt_lits.len();
        if 30 < len {
            return;
        }
        unsafe {
            let key = self.an_level_map_key;
            let vec = &mut self.an_learnt_lits as *mut Vec<Lit>;
            let nblevel = self.lbd_vec(&*vec);
            if 6 < nblevel {
                return;
            }
            let l0 = self.an_learnt_lits[0];
            let p: Lit = l0.negate();
            for i in 1..len {
                self.mi_var_map[(*vec)[i].vi() as usize] = key;
            }
            let mut nb = 0;
            let mut cix = self.cp[ClauseKind::Binclause as usize].watcher[p as usize];
            while cix != NULL_CLAUSE {
                let c = &self.cp[ClauseKind::Binclause as usize].clauses[cix];
                let other = if c.lit[0] == p { c.lit[1] } else { c.lit[0] };
                let vi = other.vi();
                if self.mi_var_map[vi] == key && self.vars.assigned(other) == LTRUE {
                    nb += 1;
                    self.mi_var_map[vi] -= 1;
                }
                cix = if c.lit[0] == l0 {
                    c.next_watcher[0]
                } else {
                    debug_assert_eq!(c.lit[1], l0);
                    c.next_watcher[1]
                };
            }
            if 0 < nb {
                (*vec).retain(|l| *l == l0 || self.mi_var_map[l.vi()] == key);
            }
        }
    }

    pub fn uncheck_enqueue(&mut self, l: Lit, cid: ClauseId) -> () {
        debug_assert!(l != 0, "Null literal is about to be equeued");
        let dl = self.decision_level();
        let v = &mut self.vars[l.vi()];
        v.assign = l.lbool();
        v.level = dl;
        v.reason = cid;
        mref!(self.cp, cid).set_flag(ClauseFlag::Locked, true);
        self.trail.push(l);
    }
    pub fn uncheck_assume(&mut self, l: Lit) -> () {
        self.trail_lim.push(self.trail.len());
        self.uncheck_enqueue(l, NULL_CLAUSE);
    }
}

impl Dump for Solver {
    fn dump(&self, str: &str) -> () {
        println!("# {} at {}", str, self.decision_level());
        println!(
            "# nassigns {}, decision cands {}",
            self.num_assigns(),
            self.var_order.len()
        );
        let v = self.trail.iter().map(|l| l.int()).collect::<Vec<i32>>();
        let len = self.trail_lim.len();
        if 0 < len {
            print!("# - trail[{}]  [", self.trail.len());
            if 0 < self.trail_lim[0] {
                print!("0{:?}, ", &self.trail[0..self.trail_lim[0]]);
            }
            for i in 0..(len - 1) {
                print!(
                    "{}{:?}, ",
                    i + 1,
                    &v[self.trail_lim[i]..self.trail_lim[i + 1]]
                );
            }
            println!("{}{:?}]", len, &v[self.trail_lim[len - 1]..]);
        } else {
            println!("# - trail[  0]  [0{:?}]", &v);
        }
        println!("- trail_lim  {:?}", self.trail_lim);
        if false {
            // TODO: dump watches links
        }
        if false {
            self.var_order.dump();
            // self.var_order.check("");
        }
    }
}

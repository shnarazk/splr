use clause::*;
use types::*;
use var::*;

/// In splr, the watch map is reseted at the beginning of every simplification phase.
/// It's just a immutable index (with some data) referring to a Clause in a Vec.
#[derive(Debug)]
pub struct Watch {
    pub other: Lit,
    pub by: ClauseIndex,
    pub to: Lit,
}

impl Watch {
    pub fn new(o: Lit, b: ClauseIndex) -> Watch {
        Watch {
            other: o,
            by: b,
            to: NULL_LIT,
        }
    }
}

/// is a mapping from `Lit` to `Vec<Watch>`.
type WatchMap = Vec<Vec<Watch>>;

/// returns `WatchMap`, or `Vec<Vec<Watch>>`.
pub fn new_watch_map(nv: usize) -> WatchMap {
    let mut vec = Vec::new();
    for _i in 0..2 * nv + 1 {
        vec.push(Vec::new());
    }
    vec
}

pub fn push_to_watch(w: &mut [Vec<Watch>], ci: ClauseIndex, w0: Lit, w1: Lit) -> () {
    if ci == NULL_CLAUSE {
        return;
    }
    w[w0.negate() as usize].push(Watch::new(w1, ci));
    w[w1.negate() as usize].push(Watch::new(w0, ci));
}

/// is the collection of all variables.
#[derive(Debug)]
pub struct Solver {
    /// Assignment Management
    pub vars: Vec<Var>,
    pub clauses: ClauseManager,
    pub fixed_len: usize,
    pub watches: WatchMap,
    pub trail: Vec<Lit>,
    pub trail_lim: Vec<usize>,
    pub q_head: usize,
    pub conflicts: Vec<Lit>,
    /// Variable Order
    pub var_order: VarIndexHeap,
    /// Configuration
    pub config: SolverConfiguration,
    pub num_vars: usize,
    pub cla_inc: f64,
    pub var_inc: f64,
    pub root_level: usize,
    /// Database Management
    pub clause_permutation: Vec<usize>,
    pub learnt_size_adj: f64,
    pub learnt_size_cnt: u64,
    pub max_learnts: f64,
    pub num_solved_vars: usize,
    /// Working memory
    pub ok: bool,
    pub an_seen: Vec<Lit>,
    pub an_to_clear: Vec<Lit>,
    pub an_stack: Vec<Lit>,
    pub an_last_dl: Vec<Lit>,
    pub an_learnt_lits: Vec<Lit>,
    pub stats: Vec<i64>,
    pub lbd_seen: Vec<u64>,
    pub lbd_key: u64,
    /// restart heuristics
    pub asg_f: Ema_,
    pub asg_s: Ema,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub lbd_f: Ema_,
    pub lbd_s: Ema,
    pub next_restart: u64,
    pub restart_exp: f64,
    pub rbias: Ema_,
}

trait Dump {
    fn dump(&self, mes: &str) -> ();
}

impl Solver {
    pub fn new(cfg: SolverConfiguration, cnf: &CNFDescription) -> Solver {
        let nv = cnf.num_of_variables as usize;
        let nc = cnf.num_of_clauses as usize;
        let (fe, se) = cfg.ema_coeffs;
        let re = cfg.restart_expansion;
        let cdr = cfg.clause_decay_rate;
        let vdr = cfg.variable_decay_rate;
        let s = Solver {
            vars: Var::new_vars(nv),
            clauses: new_clause_manager(nc),
            fixed_len: 1 + nc,
            watches: new_watch_map(nv * 2),
            trail: Vec::with_capacity(nv),
            trail_lim: Vec::new(),
            q_head: 0,
            conflicts: vec![],
            var_order: VarIndexHeap::new(nv),
            config: cfg,
            num_vars: nv,
            cla_inc: cdr,
            var_inc: vdr,
            root_level: 0,
            clause_permutation: (0..nc * 2).collect(),
            learnt_size_adj: 100.0,
            learnt_size_cnt: 100,
            max_learnts: 2000.0,
            num_solved_vars: 0,
            ok: true,
            an_seen: vec![0; nv + 1],
            an_to_clear: vec![0; nv + 1],
            an_stack: vec![],
            an_last_dl: vec![],
            an_learnt_lits: vec![],
            stats: vec![0; StatIndex::EndOfStatIndex as usize],
            lbd_seen: vec![0; nv + 1],
            lbd_key: 0,
            asg_f: Ema_::new(fe),
            asg_s: Ema::new(se),
            b_lvl: Ema::new(fe),
            c_lvl: Ema::new(fe),
            lbd_f: Ema_::new(fe),
            lbd_s: Ema::new(se),
            next_restart: 100,
            restart_exp: re,
            rbias: Ema_::new(se),
        };
        s
    }
    pub fn assigned(&self, l: Lit) -> Lbool {
        let x = self.vars[l.vi()].assign;
        if x == BOTTOM {
            BOTTOM
        } else if l.positive() {
            x
        } else {
            negate_bool(x)
        }
    }
    pub fn satisfies(&self, c: &Clause) -> bool {
        for l in &c.lits {
            if self.assigned(*l) == LTRUE {
                return true;
            }
        }
        false
    }
    pub fn inject(&mut self, mut c: Clause) -> ClauseIndex {
        if c.lits.len() == 1 {
            self.enqueue(c.lits[0], NULL_CLAUSE);
            return 0;
        }
        let w0 = c.lits[0];
        let w1 = c.lits[1];
        let ci = self.clauses.len();
        c.index = ci;
        // println!("Inject {}-th clause {}.", ci, c);
        self.clauses.push(c);
        push_to_watch(&mut self.watches, ci, w0, w1);
        ci
    }
    pub fn num_assigns(&self) -> usize {
        self.trail.len()
    }
    /// the number of given clause
    /// The numeber might change after simplification
    pub fn num_givencs(&self) -> usize {
        self.fixed_len
    }
    pub fn num_learnts(&self) -> usize {
        self.clauses.len() - self.fixed_len - 1 // 1 for NULL_CLAUSE
    }
    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }
    pub fn enqueue(&mut self, l: Lit, cid: ClauseIndex) -> bool {
        // println!("enqueue: {} by {}", l.int(), cid);
        let sig = l.lbool();
        let val = self.vars[l.vi()].assign;
        if val == BOTTOM {
            {
                let dl = self.decision_level();
                let v = &mut self.vars[l.vi()];
                v.assign = sig;
                v.level = dl;
                v.reason = cid;
            }
            self.trail.push(l);
            true
        } else {
            val == sig
        }
    }
    pub fn assume(&mut self, l: Lit) -> bool {
        self.trail_lim.push(self.trail.len());
        self.enqueue(l, NULL_CLAUSE)
    }
    pub fn cancel_until(&mut self, lv: usize) -> () {
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
                v.reason = NULL_CLAUSE;
            }
            self.var_order.insert(&self.vars, vi);
        }
        self.trail.truncate(lim); // FIXME
        self.trail_lim.truncate(lv);
        self.q_head = lim;
        // self.dump("cancel_until");
    }
    /// Heap operations; renamed from selectVO
    pub fn select_var(&mut self) -> VarIndex {
        loop {
            // self.var_order.check("select_var 1");
            if self.var_order.len() == 0 {
                // println!("> select_var returns 0");
                return 0;
            }
            let vi = self.var_order.root(&self.vars);
            // self.var_order.check("select_var 2");
            let x = self.vars[vi].assign;
            if x == BOTTOM {
                return vi;
            }
        }
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
            for (i, m) in self.watches.iter().enumerate() {
                if !m.is_empty() {
                    println!(
                        "# - watches[{:>3}] => {:?}",
                        (i as Lit).int(),
                        m.iter().map(|w| w.by).collect::<Vec<ClauseIndex>>()
                    );
                }
            }
        }
        if false {
            self.var_order.dump();
            self.var_order.check("");
        }
    }
}

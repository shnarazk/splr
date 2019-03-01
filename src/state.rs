use crate::clause::ClauseDB;
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::restart::Ema;
use crate::traits::*;
use crate::types::*;
use crate::var::Var;
use std::fmt;
use std::io::{stdout, Write};
use std::path::Path;
use std::time::SystemTime;

/// A collection of named search heuristics
#[derive(Debug, Eq, PartialEq)]
pub enum SearchStrategy {
    Initial,
    Generic,
    LowDecisions,
    HighSuccesive,
    LowSuccesive,
    ManyGlues,
}

impl SearchStrategy {
    pub fn to_str(&self) -> &'static str {
        match self {
            SearchStrategy::Initial => "in the initial search phase to determine a main strategy",
            SearchStrategy::Generic => "generic (using the generic parameter set)",
            SearchStrategy::LowDecisions => "LowDecs (many conflicts at low levels, using CSh)",
            SearchStrategy::HighSuccesive => "HighSucc (long decision chains)",
            SearchStrategy::LowSuccesive => "LowSucc (successive conflicts, using Luby)",
            SearchStrategy::ManyGlues => "ManyGlue (many glue clauses)",
        }
    }
}

/// stat index
#[derive(Clone, Eq, PartialEq)]
pub enum Stat {
    Conflict = 0,          // the number of backjump
    Decision,              // the number of decision
    Restart,               // the number of restart
    RestartRecord,         // the last recorded number of Restart
    BlockRestart,          // the number of blacking start
    BlockRestartRecord,    // the last recorded number of BlockResatr
    Learnt,                // the number of learnt clauses (< Conflict)
    NoDecisionConflict,    // the number of 'no decision conflict'
    Propagation,           // the number of propagation
    Reduction,             // the number of reduction
    SatClauseElimination,  // the number of good old simplification
    ExhaustiveElimination, // the number of clause subsumption and varibale elimination
    Assign,                // the number of assigned variables
    SolvedRecord,          // the last number of solved variables
    SumLBD,                // the sum of generated learnts' LBD
    NumBin,                // the number of binary clauses
    NumBinLearnt,          // the number of binary learnt clauses
    NumLBD2,               // the number of clauses which LBD is 2
    EndOfStatIndex,        // Don't use this dummy.
}

/// Data storage for `Solver`
#[derive(Debug)]
pub struct State {
    pub root_level: usize,
    pub num_vars: usize,
    /// STARATEGY
    pub adapt_strategy: bool,
    pub strategy: SearchStrategy,
    pub use_chan_seok: bool,
    pub co_lbd_bound: usize,
    pub lbd_frozen_clause: usize,
    /// CLAUSE/VARIABLE ACTIVITY
    pub cla_decay: f64,
    pub cla_inc: f64,
    pub var_decay: f64,
    pub var_decay_max: f64,
    pub var_inc: f64,
    /// CLAUSE REDUCTION
    pub first_reduction: usize,
    pub glureduce: bool,
    pub cdb_inc: usize,
    pub cdb_inc_extra: usize,
    pub cdb_soft_limit: usize,
    pub ema_coeffs: (i32, i32),
    /// RESTART
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glusoce
    pub restart_thr: f64,
    /// For block restart based on average assigments: 1.40.
    /// This is called `R` in Glucose
    pub restart_blk: f64,
    pub restart_asg_len: usize,
    pub restart_lbd_len: usize,
    pub restart_expansion: f64,
    pub restart_step: usize,
    pub luby_restart: bool,
    pub luby_restart_num_conflict: f64,
    pub luby_restart_inc: f64,
    pub luby_current_restarts: usize,
    pub luby_restart_factor: f64,
    /// Eliminator
    pub use_elim: bool,
    /// 0 for no limit
    /// Stop elimination if a generated resolvent is larger than this
    /// 0 means no limit.
    pub elim_eliminate_combination_limit: usize,
    /// Stop elimination if the increase of clauses is over this
    pub elim_eliminate_grow_limit: usize,
    pub elim_eliminate_loop_limit: usize,
    /// Stop sumsumption if the size of a clause is over this
    pub elim_subsume_literal_limit: usize,
    pub elim_subsume_loop_limit: usize,
    /// MISC
    pub ok: bool,
    pub next_reduction: usize, // renamed from `nbclausesbeforereduce`
    pub next_restart: usize,
    pub cur_restart: usize,
    pub after_restart: usize,
    pub elim_trigger: usize,
    pub stagnation: usize,
    pub stats: [usize; Stat::EndOfStatIndex as usize], // statistics
    pub ema_asg: Ema,
    pub ema_lbd: Ema,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub sum_asg: f64,
    pub num_solved_vars: usize,
    pub num_eliminated_vars: usize,
    pub model: Vec<Lbool>,
    pub conflicts: Vec<Lit>,
    pub new_learnt: Vec<Lit>,
    pub an_seen: Vec<bool>,
    pub lbd_temp: Vec<usize>,
    pub last_dl: Vec<Lit>,
    pub start: SystemTime,
    pub dumper: ProgressRecord,
    pub use_progress: bool,
    pub progress_cnt: usize,
    pub progress_log: bool,
    pub target: CNFDescription,
}

macro_rules! i {
    ($format: expr, $dumper: expr, $key: expr, $val: expr) => {
        match $val {
            v => {
                let ptr = &mut $dumper.vali[$key as usize];
                if (v as f64) * 1.6 < *ptr as f64 {
                    *ptr = v;
                    format!("\x1B[001m\x1B[031m{}\x1B[000m", format!($format, *ptr))
                } else if v < *ptr {
                    *ptr = v;
                    format!("\x1B[031m{}\x1B[000m", format!($format, *ptr))
                } else if (*ptr as f64) * 1.6 < v as f64 {
                    *ptr = v;
                    format!("\x1B[001m\x1B[034m{}\x1B[000m", format!($format, *ptr))
                } else if *ptr < v {
                    *ptr = v;
                    format!("\x1B[034m{}\x1B[000m", format!($format, *ptr))
                } else {
                    *ptr = v;
                    format!($format, *ptr)
                }
            }
        }
    };
}

macro_rules! f {
    ($format: expr, $dumper: expr, $key: expr, $val: expr) => {
        match $val {
            v => {
                let ptr = &mut $dumper.valf[$key as usize];
                if v * 1.6 < *ptr {
                    *ptr = v;
                    format!("\x1B[001m\x1B[031m{}\x1B[000m", format!($format, *ptr))
                } else if v < *ptr {
                    *ptr = v;
                    format!("\x1B[031m{}\x1B[000m", format!($format, *ptr))
                } else if *ptr * 1.6 < v {
                    *ptr = v;
                    format!("\x1B[001m\x1B[034m{}\x1B[000m", format!($format, *ptr))
                } else if *ptr < v {
                    *ptr = v;
                    format!("\x1B[034m{}\x1B[000m", format!($format, *ptr))
                } else {
                    *ptr = v;
                    format!($format, *ptr)
                }
            }
        }
    };
}

impl Default for State {
    fn default() -> State {
        State {
            root_level: 0,
            num_vars: 0,
            adapt_strategy: true,
            strategy: SearchStrategy::Initial,
            use_chan_seok: false,
            co_lbd_bound: 5,
            lbd_frozen_clause: 30,
            cla_decay: 0.999,
            cla_inc: 1.0,
            var_decay: 0.9,
            var_decay_max: 0.95,
            var_inc: 0.9,
            first_reduction: 1000,
            glureduce: true,
            cdb_inc: 300,
            cdb_inc_extra: 1000,
            cdb_soft_limit: 0,     // 248_000_000
            restart_thr: 0.60,     // will be overwrited by bin/splr
            restart_blk: 1.40,     // will be overwrited by bin/splr
            restart_asg_len: 3500, // will be overwrited by bin/splr
            restart_lbd_len: 100,  // will be overwrited by bin/splr
            restart_expansion: 1.15,
            restart_step: 50,
            luby_restart: false,
            luby_restart_num_conflict: 0.0,
            luby_restart_inc: 2.0,
            luby_current_restarts: 0,
            luby_restart_factor: 100.0,
            ema_coeffs: (2 ^ 5, 2 ^ 15),
            use_elim: true,
            elim_eliminate_combination_limit: 80,
            elim_eliminate_grow_limit: 0, // 64
            elim_eliminate_loop_limit: 2_000_000,
            elim_subsume_literal_limit: 100,
            elim_subsume_loop_limit: 2_000_000,
            ok: true,
            next_reduction: 1000,
            next_restart: 100,
            cur_restart: 1,
            after_restart: 0,
            elim_trigger: 1,
            stagnation: 0,
            stats: [0; Stat::EndOfStatIndex as usize],
            ema_asg: Ema::new(1),
            ema_lbd: Ema::new(1),
            b_lvl: Ema::new(5_000),
            c_lvl: Ema::new(5_000),
            sum_asg: 0.0,
            num_solved_vars: 0,
            num_eliminated_vars: 0,
            model: Vec::new(),
            conflicts: Vec::new(),
            new_learnt: Vec::new(),
            an_seen: Vec::new(),
            lbd_temp: Vec::new(),
            last_dl: Vec::new(),
            start: SystemTime::now(),
            use_progress: true,
            progress_cnt: 0,
            progress_log: false,
            dumper: ProgressRecord::default(),
            target: CNFDescription::default(),
        }
    }
}

impl StateIF for State {
    fn new(config: &Config, mut cnf: CNFDescription) -> State {
        let mut state = State::default();
        cnf.pathname = if cnf.pathname == "" {
            "--".to_string()
        } else {
            Path::new(&cnf.pathname)
                .file_name()
                .unwrap()
                .to_os_string()
                .into_string()
                .unwrap()
        };
        state.num_vars = cnf.num_of_variables;
        state.adapt_strategy = !config.no_adapt;
        state.cdb_soft_limit = config.clause_limit;
        state.elim_eliminate_grow_limit = config.elim_grow_limit;
        state.elim_subsume_literal_limit = config.elim_lit_limit;
        state.restart_thr = config.restart_threshold;
        state.restart_blk = config.restart_blocking;
        state.restart_asg_len = config.restart_asg_samples;
        state.restart_lbd_len = config.restart_lbd_samples;
        state.restart_step = config.restart_step;
        state.progress_log = config.use_log;
        state.use_elim = !config.no_elim;
        state.ema_asg = Ema::new(config.restart_asg_samples);
        state.ema_lbd = Ema::new(config.restart_lbd_samples);
        state.model = vec![BOTTOM; cnf.num_of_variables + 1];
        state.an_seen = vec![false; cnf.num_of_variables + 1];
        state.lbd_temp = vec![0; cnf.num_of_variables + 1];
        state.target = cnf;
        state
    }
    fn adapt(&mut self, cdb: &mut ClauseDB) {
        if !self.adapt_strategy || self.strategy != SearchStrategy::Initial {
            return;
        }
        let mut re_init = false;
        let decpc =
            self.stats[Stat::Decision as usize] as f64 / self.stats[Stat::Conflict as usize] as f64;
        if decpc <= 1.2 {
            self.strategy = SearchStrategy::LowDecisions;
            self.use_chan_seok = true;
            self.co_lbd_bound = 4;
            self.glureduce = true;
            self.first_reduction = 2000;
            self.next_reduction = 2000;
            self.cur_restart = (self.stats[Stat::Conflict as usize] as f64
                / self.next_reduction as f64
                + 1.0) as usize;
            self.cdb_inc = 0;
            re_init = true;
        }
        if self.stats[Stat::NoDecisionConflict as usize] < 30_000 {
            self.strategy = SearchStrategy::LowSuccesive;
            self.luby_restart = true;
            self.luby_restart_factor = 100.0;
            self.var_decay = 0.999;
            self.var_decay_max = 0.999;
        }
        if self.stats[Stat::NoDecisionConflict as usize] > 54_400 {
            self.strategy = SearchStrategy::HighSuccesive;
            self.use_chan_seok = true;
            self.glureduce = true;
            self.co_lbd_bound = 3;
            self.first_reduction = 30000;
            self.var_decay = 0.99;
            self.var_decay_max = 0.99;
            // randomize_on_restarts = 1;
        }
        if self.stats[Stat::NumLBD2 as usize] - self.stats[Stat::NumBin as usize] > 20_000 {
            self.strategy = SearchStrategy::ManyGlues;
            self.var_decay = 0.91;
            self.var_decay_max = 0.91;
        }
        if self.strategy == SearchStrategy::Initial {
            self.strategy = SearchStrategy::Generic;
            return;
        }
        if self.use_chan_seok {
            // Adjusting for low decision levels.
            // move some clauses with good lbd (col_lbd_bound) to Permanent
            for c in &mut cdb.clause[1..] {
                if c.is(Flag::DEAD) || !c.is(Flag::LEARNT) {
                    continue;
                }
                if c.rank <= self.co_lbd_bound {
                    c.turn_off(Flag::LEARNT);
                    cdb.num_learnt -= 1;
                } else if re_init {
                    c.kill(&mut cdb.touched);
                }
            }
            cdb.garbage_collect();
        }
    }
    fn progress_header(&self) {
        if !self.use_progress {
            return;
        }
        if self.progress_log {
            self.dump_header();
            return;
        }
        println!("{}", self);
        println!("                                                  ");
        println!("                                                  ");
        println!("                                                  ");
        println!("                                                  ");
        println!("                                                  ");
        println!("                                                  ");
        println!("                                                  ");
    }
    fn flush(&self, mes: &str) {
        if self.use_progress && !self.progress_log {
            // print!("\x1B[1G{}", mes);
            print!("{}", mes);
            stdout().flush().unwrap();
        }
    }
    /// `mes` should be shorter than or equal to 9, or 8 + a delimitor.
    #[allow(clippy::cyclomatic_complexity)]
    fn progress(&mut self, cdb: &ClauseDB, vars: &[Var], mes: Option<&str>) {
        if !self.use_progress {
            return;
        }
        if self.progress_log {
            self.dump(cdb, vars);
            return;
        }
        let nv = vars.len() - 1;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        self.progress_cnt += 1;
        print!("\x1B[8A\x1B[1G");
        let msg = match mes {
            None => self.strategy.to_str(),
            Some(x) => x,
        };
        let count = self.stats[Stat::Conflict as usize];
        let ave = self.stats[Stat::SumLBD as usize] as f64 / count as f64;
        println!("\x1B[2K{}", self);
        println!(
            "\x1B[2K #conflict:{}, #decision:{}, #propagate:{} ",
            i!(
                "{:>11}",
                self.dumper,
                LogUsizeId::Conflict,
                self.stats[Stat::Conflict as usize]
            ),
            i!(
                "{:>13}",
                self.dumper,
                LogUsizeId::Decision,
                self.stats[Stat::Decision as usize]
            ),
            i!(
                "{:>15}",
                self.dumper,
                LogUsizeId::Propagate,
                self.stats[Stat::Propagation as usize]
            ),
        );
        println!(
            "\x1B[2K  Assignment|#rem:{}, #fix:{}, #elm:{}, prg%:{} ",
            i!("{:>9}", self.dumper, LogUsizeId::Remain, nv - sum),
            i!("{:>9}", self.dumper, LogUsizeId::Fixed, fixed),
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::Eliminated,
                self.num_eliminated_vars
            ),
            f!(
                "{:>9.4}",
                self.dumper,
                LogF64Id::Progress,
                (sum as f64) / (nv as f64) * 100.0
            ),
        );
        println!(
            "\x1B[2K Clause Kind|Remv:{}, LBD2:{}, Binc:{}, Perm:{} ",
            i!("{:>9}", self.dumper, LogUsizeId::Removable, cdb.num_learnt),
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::LBD2,
                self.stats[Stat::NumLBD2 as usize]
            ),
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::Binclause,
                self.stats[Stat::NumBinLearnt as usize]
            ),
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::Permanent,
                cdb.num_active - cdb.num_learnt
            ),
        );
        println!(
            "\x1B[2K     Restart|#BLK:{}, #RST:{}, eASG:{}, eLBD:{} ",
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::RestartBlock,
                self.stats[Stat::BlockRestart as usize]
            ),
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::Restart,
                self.stats[Stat::Restart as usize]
            ),
            f!(
                "{:>9.4}",
                self.dumper,
                LogF64Id::EmaAsg,
                self.ema_asg.get() / nv as f64
            ),
            f!(
                "{:>9.4}",
                self.dumper,
                LogF64Id::EmaLBD,
                self.ema_lbd.get() / ave
            ),
        );
        println!(
            "\x1B[2K   Conflicts|aLBD:{}, bjmp:{}, cnfl:{} |blkR:{} ",
            f!("{:>9.2}", self.dumper, LogF64Id::AveLBD, self.ema_lbd.get()),
            f!("{:>9.2}", self.dumper, LogF64Id::BLevel, self.b_lvl.get()),
            f!("{:>9.2}", self.dumper, LogF64Id::CLevel, self.c_lvl.get()),
            f!(
                "{:>9.4}",
                self.dumper,
                LogF64Id::RestartBlkR,
                self.restart_blk
            ),
        );
        println!(
            "\x1B[2K   Clause DB|#rdc:{}, #sce:{}, #exe:{} |frcK:{} ",
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::Reduction,
                self.stats[Stat::Reduction as usize]
            ),
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::SatClauseElim,
                self.stats[Stat::SatClauseElimination as usize]
            ),
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::ExhaustiveElim,
                self.stats[Stat::ExhaustiveElimination as usize]
            ),
            f!(
                "{:>9.4}",
                self.dumper,
                LogF64Id::RestartThrK,
                self.restart_thr
            ),
        );
        println!("\x1B[2K    Strategy|mode: {}", msg);
        self.flush("\x1B[2K");
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tm = match self.start.elapsed() {
            Ok(e) => e.as_secs() as f64 + f64::from(e.subsec_millis()) / 1000.0f64,
            Err(_) => 0.0f64,
        };
        let vc = format!(
            "{},{}",
            self.target.num_of_variables, self.target.num_of_clauses,
        );
        let vclen = vc.len();
        let fnlen = self.target.pathname.len();
        let width = 59;
        if width < vclen + fnlen + 1 {
            write!(
                f,
                "{:<w$} |time:{:>9.2}",
                self.target.pathname,
                tm,
                w = width
            )
        } else {
            write!(
                f,
                "{}{:>w$} |time:{:>9.2}",
                self.target.pathname,
                &vc,
                tm,
                w = width - fnlen,
            )
        }
    }
}

/// Index for `Usize` data, used in `ProgressRecord`
pub enum LogUsizeId {
    Propagate = 0,  //  0: propagate: usize,
    Decision,       //  1: decision: usize,
    Conflict,       //  2: conflict: usize,
    Remain,         //  3: remain: usize,
    Fixed,          //  4: fixed: usize,
    Eliminated,     //  5: elim: usize,
    Removable,      //  6: removable: usize,
    LBD2,           //  7: lbd2: usize,
    Binclause,      //  8: binclause: usize,
    Permanent,      //  9: permanent: usize,
    RestartBlock,   // 10: restart_block: usize,
    Restart,        // 11: restart_count: usize,
    Reduction,      // 12: reduction: usize,
    SatClauseElim,  // 13: simplification: usize,
    ExhaustiveElim, // 14: elimination: usize,
    // ElimClauseQueue, // 15: elim_clause_queue: usize,
    // ElimVarQueue, // 16: elim_var_queue: usize,
    End,
}

/// Index for `f64` data, used in `ProgressRecord`
pub enum LogF64Id {
    Progress = 0, //  0: progress: f64,
    EmaAsg,       //  1: ema_asg: f64,
    EmaLBD,       //  2: ema_lbd: f64,
    AveLBD,       //  3: ave_lbd: f64,
    BLevel,       //  4: backjump_level: f64,
    CLevel,       //  5: conflict_level: f64,
    RestartThrK,  //  6: restart K
    RestartBlkR,  //  7: restart R
    End,
}

/// Record of old stats.
#[derive(Debug)]
pub struct ProgressRecord {
    pub vali: [usize; LogUsizeId::End as usize],
    pub valf: [f64; LogF64Id::End as usize],
}

impl Default for ProgressRecord {
    fn default() -> ProgressRecord {
        ProgressRecord {
            vali: [0; LogUsizeId::End as usize],
            valf: [0.0; LogF64Id::End as usize],
        }
    }
}

impl State {
    #[allow(dead_code)]
    fn dump_header_details(&self) {
        println!(
            "   #mode,         Variable Assignment      ,,  \
             Clause Database ent  ,,  Restart Strategy       ,, \
             Misc Progress Parameters,,   Eliminator"
        );
        println!(
            "   #init,    #remain,#solved,  #elim,total%,,#learnt,  \
             #perm,#binary,,block,force, #asgn,  lbd/,,    lbd, \
             back lv, conf lv,,clause,   var"
        );
    }
    fn dump_header(&self) {
        println!(
            "c |          RESTARTS           |          ORIGINAL         |              LEARNT              | Progress |\n\
             c |       NB   Blocked  Avg Cfc |    Vars  Clauses Literals |   Red   Learnts    LBD2  Removed |          |\n\
             c ========================================================================================================="
        );
    }
    fn dump(&mut self, cdb: &ClauseDB, vars: &[Var]) {
        self.progress_cnt += 1;
        let nv = vars.len() - 1;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        let nlearnts = cdb.countf(Flag::LEARNT); // TODO eliminate DEAD
        let ncnfl = self.stats[Stat::Conflict as usize];
        let nrestart = self.stats[Stat::Restart as usize];
        println!(
            "c | {:>8}  {:>8} {:>8} | {:>7} {:>8} {:>8} |  {:>4}  {:>8} {:>7} {:>8} | {:>6.3} % |",
            nrestart,                                // restart
            self.stats[Stat::BlockRestart as usize], // blocked
            ncnfl / nrestart.max(1),                 // average cfc (Conflict / Restart)
            nv - fixed - self.num_eliminated_vars,   // alive vars
            cdb.count(true) - nlearnts,              // given clauses
            0,                                       // alive literals
            self.stats[Stat::Reduction as usize],    // clause reduction
            nlearnts,                                // alive learnts
            self.stats[Stat::NumLBD2 as usize],      // learnts with LBD = 2
            ncnfl - nlearnts,                        // removed learnts
            (sum as f32) / (nv as f32) * 100.0,      // progress
        );
    }
    #[allow(dead_code)]
    fn dump_details(&mut self, cdb: &ClauseDB, elim: &Eliminator, vars: &[Var], mes: Option<&str>) {
        self.progress_cnt += 1;
        let msg = match mes {
            None => self.strategy.to_str(),
            Some(x) => x,
        };
        let nv = vars.len() - 1;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        println!(
            "{:>3}#{:>8},{:>7},{:>7},{:>7},{:>6.3},,{:>7},{:>7},\
             {:>7},,{:>5},{:>5},{:>6.2},{:>6.2},,{:>7.2},{:>8.2},{:>8.2},,\
             {:>6},{:>6}",
            self.progress_cnt,
            msg,
            nv - sum,
            fixed,
            self.num_eliminated_vars,
            (sum as f32) / (nv as f32) * 100.0,
            cdb.num_learnt,
            cdb.num_active,
            0,
            self.stats[Stat::BlockRestart as usize],
            self.stats[Stat::Restart as usize],
            self.ema_asg.get(),
            self.ema_lbd.get(),
            self.ema_lbd.get(),
            self.b_lvl.get(),
            self.c_lvl.get(),
            elim.clause_queue_len(),
            elim.var_queue_len(),
        );
    }
}

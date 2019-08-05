use crate::clause::ClauseDB;
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::restart::{Ema, Ema2};
use crate::traits::*;
use crate::types::*;
use crate::var::VarDB;
use libc::{clock_gettime, timespec, CLOCK_PROCESS_CPUTIME_ID};
use std::cmp::Ordering;
use std::fmt;
use std::io::{stdout, Write};
use std::ops::{Index, IndexMut};
use std::path::Path;
use std::time::SystemTime;

/// A collection of named search heuristics
#[derive(Debug, Eq, PartialEq)]
pub enum SearchStrategy {
    /// the initial search phase to determine a main strategy
    Initial,
    /// Non-Specific-Instance using generic settings
    Generic,
    /// Many-Low-Level-Conflicts using Chan Seok heuristics
    LowDecisions,
    /// High-Successive-Conflicts using Chan Seok heuristics
    HighSuccesive,
    /// Low-Successive-Conflicts w/ Luby sequence
    LowSuccesiveLuby,
    /// Low-Successive-Conflicts w/o Luby sequence
    LowSuccesiveM,
    /// Many-Glue-Clauses
    ManyGlues,
}

impl fmt::Display for SearchStrategy {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        if formatter.alternate() {
            write!(
                formatter,
                "{}",
                match self {
                    SearchStrategy::Initial => {
                        "in the initial search phase to determine a main strategy"
                    }
                    SearchStrategy::Generic => "Non-Specific-Instance using generic settings",
                    SearchStrategy::LowDecisions => {
                        "Many-Low-Level-Conflicts using Chan Seok heuristics"
                    }
                    SearchStrategy::HighSuccesive => {
                        "High-Successive-Conflicts using Chan Seok heuristics"
                    }
                    SearchStrategy::LowSuccesiveLuby => {
                        "Low-Successive-Conflicts-Luby w/ Luby sequence"
                    }
                    SearchStrategy::LowSuccesiveM => {
                        "Low-Successive-Conflicts-Modified w/o Luby sequence"
                    }
                    SearchStrategy::ManyGlues => "Many-Glue-Clauses",
                }
            )
        } else {
            let name = match self {
                SearchStrategy::Initial => "initial",
                SearchStrategy::Generic => "generic",
                SearchStrategy::LowDecisions => "LowDecs",
                SearchStrategy::HighSuccesive => "HighSucc",
                SearchStrategy::LowSuccesiveLuby => "LowSuccLuby",
                SearchStrategy::LowSuccesiveM => "LowSuccM",
                SearchStrategy::ManyGlues => "ManyGlue",
            };
            if let Some(w) = formatter.width() {
                match name.len().cmp(&w) {
                    Ordering::Equal => write!(formatter, "{}", name),
                    Ordering::Less => write!(formatter, "{}{}", " ".repeat(w - name.len()), name),
                    Ordering::Greater => write!(formatter, "{}", &name[..w]),
                }
            } else {
                write!(formatter, "{}", name)
            }
        }
    }
}

impl SearchStrategy {
    pub fn to_str(&self) -> &'static str {
        match self {
            SearchStrategy::Initial => "in the initial search phase to determine a main strategy",
            SearchStrategy::Generic => "generic (using the generic parameter set)",
            SearchStrategy::LowDecisions => "LowDecs (many conflicts at low levels, using CSh)",
            SearchStrategy::HighSuccesive => "HighSucc (long decision chains)",
            SearchStrategy::LowSuccesiveLuby => "LowSuccLuby (successive conflicts)",
            SearchStrategy::LowSuccesiveM => "LowSuccP (successive conflicts)",
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
    BlockRestartRecord,    // the last recorded number of BlockRestart
    PartialRestart,        // the number of partial restart
    LubyRestart,           // the number of Luby restart
    Learnt,                // the number of learnt clauses (< Conflict)
    NoDecisionConflict,    // the number of 'no decision conflict'
    Propagation,           // the number of propagation
    Reduction,             // the number of reduction
    SatClauseElimination,  // the number of good old simplification
    ExhaustiveElimination, // the number of clause subsumption and variable elimination
    Assign,                // the number of assigned variables
    SolvedRecord,          // the last number of solved variables
    SumASG,                // the num of the number of assignment after each backjump
    SumLBD,                // the sum of generated learnts' LBD
    NumBin,                // the number of binary clauses
    NumBinLearnt,          // the number of binary learnt clauses
    NumLBD2,               // the number of clauses which LBD is 2
    Stagnation,            // the number of stagnation
    PolarRestart,          // the number of restart by polarization
    EndOfStatIndex,        // Don't use this dummy.
}

impl Index<Stat> for [usize] {
    type Output = usize;
    fn index(&self, i: Stat) -> &usize {
        &self[i as usize]
    }
}

impl IndexMut<Stat> for [usize] {
    fn index_mut(&mut self, i: Stat) -> &mut usize {
        &mut self[i as usize]
    }
}

/// Data storage for `Solver`
#[derive(Debug)]
pub struct State {
    pub root_level: usize,
    pub num_vars: usize,
    /// STRATEGY
    pub use_adapt_strategy: bool,
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
    pub adaptive_restart: bool,
    /// For force restart based on average LBD of newly generated clauses: 0.80.
    /// This is called `K` in Glucose
    pub restart_thr: f64,
    /// For block restart based on average assignments: 1.40.
    /// This is called `R` in Glucose
    pub restart_blk: f64,
    pub restart_asg_len: usize,
    pub restart_lbd_len: usize,
    pub restart_expansion: f64,
    pub restart_step: usize,
    pub restart_block_step: usize,
    pub use_luby_restart: bool,
    pub luby_restart_num_conflict: f64,
    pub luby_restart_inc: f64,
    pub luby_current_restarts: usize,
    pub luby_restart_factor: f64,
    pub luby_restart_cnfl_cnt: f64,
    pub use_deep_search_mode: bool,
    pub stagnated: bool,
    /// Folding computation
    pub num_partial_restart: usize,
    pub num_partial_restart_try: usize,
    pub partial_restart_ratio: Ema,
    pub ema_folds_ratio: Ema2,
    /// Eliminator
    pub use_elim: bool,
    /// 0 for no limit
    /// Stop elimination if a generated resolvent is larger than this
    /// 0 means no limit.
    pub elim_eliminate_combination_limit: usize,
    /// Stop elimination if the increase of clauses is over this
    pub elim_eliminate_grow_limit: usize,
    pub elim_eliminate_loop_limit: usize,
    /// Stop subsumption if the size of a clause is over this
    pub elim_subsume_literal_limit: usize,
    pub elim_subsume_loop_limit: usize,
    /// MISC
    pub config: Config,
    pub ok: bool,
    pub time_limit: f64,
    pub next_reduction: usize, // renamed from `nbclausesbeforereduce`
    pub next_restart: usize,
    pub cur_restart: usize,
    pub after_restart: usize,
    pub elim_trigger: usize,
    pub slack_duration: usize,
    pub stats: [usize; Stat::EndOfStatIndex as usize], // statistics
    pub ema_asg: Ema2,
    pub ema_asg_progress: Ema2,
    pub ema_lbd: Ema,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub num_solved_vars: usize,
    pub num_eliminated_vars: usize,
    pub model: Vec<Lbool>,
    pub conflicts: Vec<Lit>,
    pub new_learnt: Vec<Lit>,
    pub an_seen: Vec<bool>,
    pub last_dl: Vec<Lit>,
    pub start: SystemTime,
    pub record: ProgressRecord,
    pub use_progress: bool,
    pub progress_cnt: usize,
    pub progress_log: bool,
    pub target: CNFDescription,
    pub development_history: Vec<(usize, f64, f64, f64, f64, f64, f64, f64)>,
}

macro_rules! im {
    ($format: expr, $record: expr, $key: expr, $val: expr) => {
        match $val {
            v => {
                let ptr = &mut $record.vali[$key as usize];
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

macro_rules! i {
    ($format: expr, $record: expr, $key: expr, $val: expr) => {
        match $val {
            v => {
                let ptr = &mut $record.vali[$key as usize];
                *ptr = v;
                format!($format, *ptr)
            }
        }
    };
}

#[allow(unused_macros)]
macro_rules! f {
    ($format: expr, $record: expr, $key: expr, $val: expr) => {
        match $val {
            v => {
                let ptr = &mut $record.valf[$key as usize];
                *ptr = v;
                format!($format, *ptr)
            }
        }
    };
}

macro_rules! fm {
    ($format: expr, $record: expr, $key: expr, $val: expr) => {
        match $val {
            v => {
                let ptr = &mut $record.valf[$key as usize];
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
            use_adapt_strategy: true,
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
            cdb_soft_limit: 0, // 248_000_000
            ema_coeffs: (2 ^ 5, 2 ^ 15),
            adaptive_restart: false,
            restart_thr: 1.20,     // will be overwritten by bin/splr
            restart_blk: 1.00,     // will be overwritten by bin/splr
            restart_asg_len: 3500, // will be overwritten by bin/splr
            restart_lbd_len: 100,  // will be overwritten by bin/splr
            restart_expansion: 1.15,
            restart_step: 50,
            restart_block_step: 0,
            use_luby_restart: false,
            luby_restart_num_conflict: 0.0,
            luby_restart_inc: 2.0,
            luby_current_restarts: 0,
            luby_restart_factor: 100.0,
            luby_restart_cnfl_cnt: 0.0,
            use_deep_search_mode: true,
            stagnated: false,
            num_partial_restart: 0,
            num_partial_restart_try: 0,
            partial_restart_ratio: Ema::new(75),
            ema_folds_ratio: Ema2::new(5_000).with_fast(100).initialize1(),
            use_elim: true,
            elim_eliminate_combination_limit: 80,
            elim_eliminate_grow_limit: 0, // 64
            elim_eliminate_loop_limit: 2_000_000,
            elim_subsume_literal_limit: 100,
            elim_subsume_loop_limit: 2_000_000,
            config: Config::default(),
            ok: true,
            time_limit: 0.0,
            next_reduction: 1000,
            next_restart: 100,
            cur_restart: 1,
            after_restart: 0,
            elim_trigger: 1,
            slack_duration: 0,
            stats: [0; Stat::EndOfStatIndex as usize],
            ema_asg: Ema2::new(1),
            ema_asg_progress: Ema2::new(5_000).with_fast(100).initialize1(),
            ema_lbd: Ema::new(1),
            b_lvl: Ema::new(5_000),
            c_lvl: Ema::new(5_000),
            num_solved_vars: 0,
            num_eliminated_vars: 0,
            model: Vec::new(),
            conflicts: Vec::new(),
            new_learnt: Vec::new(),
            an_seen: Vec::new(),
            last_dl: Vec::new(),
            start: SystemTime::now(),
            use_progress: true,
            progress_cnt: 0,
            progress_log: false,
            record: ProgressRecord::default(),
            target: CNFDescription::default(),
            development_history: Vec::new(),
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
        state.adaptive_restart = !config.without_adaptive_restart;
        state.use_adapt_strategy = !config.without_adaptive_strategy;
        state.cdb_soft_limit = config.clause_limit;
        state.elim_eliminate_grow_limit = config.elim_grow_limit;
        state.elim_subsume_literal_limit = config.elim_lit_limit;
        state.restart_thr = config.restart_threshold;
        state.restart_blk = config.restart_blocking;
        state.restart_asg_len = config.restart_asg_len;
        state.restart_lbd_len = config.restart_lbd_len;
        state.restart_step = config.restart_step;
        state.use_deep_search_mode = config.with_deep_search;
        state.progress_log = config.use_log;
        state.use_elim = !config.without_elim;
        state.ema_asg = Ema2::new(200_000).with_fast(config.restart_asg_len);
        state.ema_lbd = Ema::new(config.restart_lbd_len);
        state.model = vec![BOTTOM; cnf.num_of_variables + 1];
        state.an_seen = vec![false; cnf.num_of_variables + 1];
        state.target = cnf;
        state.time_limit = config.timeout;
        state.config = config.clone();
        state
    }
    fn is_timeout(&self) -> bool {
        if self.time_limit == 0.0 {
            return false;
        }
        match self.start.elapsed() {
            Ok(e) => self.time_limit < e.as_secs() as f64,
            Err(_) => false,
        }
    }
    fn adapt_strategy(&mut self, cdb: &mut ClauseDB) {
        if !self.use_adapt_strategy || self.strategy != SearchStrategy::Initial {
            return;
        }
        let mut re_init = false;
        let decpc = self.stats[Stat::Decision] as f64 / self.stats[Stat::Conflict] as f64;
        if decpc <= 1.2 {
            self.strategy = SearchStrategy::LowDecisions;
            self.use_chan_seok = true;
            self.co_lbd_bound = 4;
            self.glureduce = true;
            self.first_reduction = 2000;
            self.next_reduction = 2000;
            self.cur_restart =
                (self.stats[Stat::Conflict] as f64 / self.next_reduction as f64 + 1.0) as usize;
            self.cdb_inc = 0;
            re_init = true;
        }
        if self.stats[Stat::NoDecisionConflict] < 20_000
        /* 30_000 */
        {
            if !self.use_deep_search_mode {
                self.strategy = SearchStrategy::LowSuccesiveLuby;
                self.use_luby_restart = true;
                self.luby_restart_factor = 100.0;
            } else {
                self.strategy = SearchStrategy::LowSuccesiveM;
            }
            self.var_decay = 0.999;
            self.var_decay_max = 0.999;
        }
        if self.stats[Stat::NoDecisionConflict] > 54_400 {
            self.strategy = SearchStrategy::HighSuccesive;
            self.use_chan_seok = true;
            self.glureduce = true;
            self.co_lbd_bound = 3;
            self.first_reduction = 30000;
            self.var_decay = 0.99;
            self.var_decay_max = 0.99;
            // randomize_on_restarts = 1;
        }
        if self.stats[Stat::NumLBD2] - self.stats[Stat::NumBin] > 20_000 {
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
        println!("                                                  ");
    }
    fn flush(&self, mes: &str) {
        if self.use_progress && !self.progress_log {
            // print!("\x1B[1G{}", mes);
            print!("{}", mes);
            stdout().flush().unwrap();
        }
    }
    /// `mes` should be shorter than or equal to 9, or 8 + a delimiter.
    #[allow(clippy::cognitive_complexity)]
    fn progress(&mut self, cdb: &ClauseDB, vdb: &VarDB, mes: Option<&str>) {
        if !self.use_progress {
            return;
        }
        if self.progress_log {
            self.dump(cdb, vdb);
            return;
        }
        let nv = vdb.vars.len() - 1;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        self.progress_cnt += 1;
        print!("\x1B[9A\x1B[1G");
        let count = self.stats[Stat::Conflict];
        let ave = self.stats[Stat::SumLBD] as f64 / count as f64;
        println!("\x1B[2K{}", self);
        println!(
            "\x1B[2K #conflict:{}, #decision:{}, #propagate:{} ",
            i!(
                "{:>11}",
                self.record,
                LogUsizeId::Conflict,
                self.stats[Stat::Conflict]
            ),
            i!(
                "{:>13}",
                self.record,
                LogUsizeId::Decision,
                self.stats[Stat::Decision]
            ),
            i!(
                "{:>15}",
                self.record,
                LogUsizeId::Propagate,
                self.stats[Stat::Propagation]
            ),
        );
        println!(
            "\x1B[2K    Progress|#rem:{}, #fix:{}, #elm:{}, prg%:{} ",
            im!("{:>9}", self.record, LogUsizeId::Remain, nv - sum),
            im!("{:>9}", self.record, LogUsizeId::Fixed, fixed),
            im!(
                "{:>9}",
                self.record,
                LogUsizeId::Eliminated,
                self.num_eliminated_vars
            ),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::Progress,
                (sum as f64) / (nv as f64) * 100.0
            ),
        );
        println!(
            "\x1B[2K Clause Kind|Remv:{}, LBD2:{}, Binc:{}, Perm:{} ",
            im!("{:>9}", self.record, LogUsizeId::Removable, cdb.num_learnt),
            im!(
                "{:>9}",
                self.record,
                LogUsizeId::LBD2,
                self.stats[Stat::NumLBD2]
            ),
            im!(
                "{:>9}",
                self.record,
                LogUsizeId::Binclause,
                self.stats[Stat::NumBinLearnt]
            ),
            im!(
                "{:>9}",
                self.record,
                LogUsizeId::Permanent,
                cdb.num_active - cdb.num_learnt
            ),
        );
        /*
                println!(
                    "\x1B[2K     Restart|#BLK:{}, thrd:{}, #RST:{}, thrd:{} ",
                    im!(
                        "{:>9}",
                        self.record,
                        LogUsizeId::RestartBlock,
                        self.stats[Stat::BlockRestart]
                    ),
                    fm!("{:>9.4}", self.record, LogF64Id::RestartBlkR, self.restart_blk),
                    im!(
                        "{:>9}",
                        self.record,
                        LogUsizeId::Restart,
                        self.stats[Stat::Restart]
                    ),
                    fm!("{:>9.4}", self.record, LogF64Id::RestartThrK, self.restart_thr),
                );
        */
        println!(
            "\x1B[2K    Conflict|cnfl:{}, bjmp:{}, aLBD:{}, trnd:{} ",
            fm!("{:>9.2}", self.record, LogF64Id::CLevel, self.c_lvl.get()),
            fm!("{:>9.2}", self.record, LogF64Id::BLevel, self.b_lvl.get()),
            fm!("{:>9.4}", self.record, LogF64Id::AveLBD, self.ema_lbd.get()),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::EmaLBD,
                self.ema_lbd.get() / ave
            ),
        );
        println!(
            "\x1B[2K  Assignment|asg%:{}, #prg:{}, trnd:{}, vdcy:{} ",
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::EmaAsg,
                100.0 * self.ema_asg.get() / nv as f64
            ),
            format!("{:>9.2}", self.ema_asg_progress.get()),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::EmaAsgTrend,
                self.ema_asg.trend()
            ),
            format!("{:>9.4}", vdb.activity_decay),
        );
        println!(
            "\x1B[2K     Folding|#all:{}, #now:{}, prob:{}, fast:{} ",
            format!("{:>9}", vdb.num_folding_vars),
            im!(
                "{:>9.2}",
                self.record,
                LogUsizeId::NumPV,
                vdb.num_current_folding_vars
            ),
            /* pol%:{}
                        fm!(
                            "{:>9.4}",
                            self.record,
                            LogF64Id::PVRatio,
                            (100 * self.num_folding_vars) as f64 / nv as f64
                        ),
            */
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::EmaPVInc,
                self.ema_folds_ratio.get()
            ),
            format!("{:>9.4}", self.ema_folds_ratio.get_fast()),
        );
        println!(
            "\x1B[2K     Restart|byAS:{}, byFV:{}, prob:{}, Luby:{} ",
            format!("{:>9}", self.stats[Stat::Restart]),
            im!(
                "{:>9}",
                self.record,
                LogUsizeId::RestartPartial,
                self.stats[Stat::PartialRestart]
            ),
            format!("{:>9.4}", self.partial_restart_ratio.get()),
            im!(
                "{:>9}",
                self.record,
                LogUsizeId::RestartLuby,
                self.stats[Stat::LubyRestart]
            ),
        );
        if let Some(m) = mes {
            println!("\x1B[2K    Strategy|mode: {}", m);
        } else {
            println!("\x1B[2K    Strategy|mode: {:#}", self.strategy);
        }
        self.flush("\x1B[2K");
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tm = {
            let mut time = timespec {
                tv_sec: 0,
                tv_nsec: 0,
            };
            if unsafe { clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &mut time) } == -1 {
                match self.start.elapsed() {
                    Ok(e) => e.as_secs() as f64 + f64::from(e.subsec_millis()) / 1000.0f64,
                    Err(_) => 0.0f64,
                }
            } else {
                time.tv_sec as f64 + time.tv_nsec as f64 / 1_000_000_000.0f64
            }
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
    Restart,        // 10: restart_count: usize,
    RestartLuby,    // 11: Luby restart
    RestartPartial, // 12: partial_restart_count: usize,
    Reduction,      // 13: reduction: usize,
    SatClauseElim,  // 14: simplification: usize,
    ExhaustiveElim, // 15: elimination: usize,
    Stagnation,     // 16: stagnation: usize,
    NumPV,          // 17: the number of Polar vars
    // ElimClauseQueue, // __: elim_clause_queue: usize,
    // ElimVarQueue, // __: elim_var_queue: usize,
    End,
}

/// Index for `f64` data, used in `ProgressRecord`
pub enum LogF64Id {
    Progress = 0, //  0: progress: f64,
    EmaAsg,       //  1: ema_asg: f64,
    EmaAsgTrend,  //  2: ema_asg_trend: f64,
    EmaLBD,       //  3: ema_lbd: f64,
    AveLBD,       //  4: ave_lbd: f64,
    BLevel,       //  5: backjump_level: f64,
    CLevel,       //  6: conflict_level: f64,
    RestartThrK,  //  7: restart K
    RestartBlkR,  //  8: restart R
    EmaRestart,   //  9: average effective restart step
    EmaPVInc,     // 10: increasing speed of the number of folding vars
    PVRatio,      // 11: the percentage of folding vars
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

impl Index<LogUsizeId> for ProgressRecord {
    type Output = usize;
    fn index(&self, i: LogUsizeId) -> &usize {
        &self.vali[i as usize]
    }
}

impl Index<LogUsizeId> for [usize] {
    type Output = usize;
    fn index(&self, i: LogUsizeId) -> &usize {
        &self[i as usize]
    }
}

impl Index<LogF64Id> for ProgressRecord {
    type Output = f64;
    fn index(&self, i: LogF64Id) -> &f64 {
        &self.valf[i as usize]
    }
}

impl Index<LogF64Id> for [f64] {
    type Output = f64;
    fn index(&self, i: LogF64Id) -> &f64 {
        &self[i as usize]
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
    fn dump(&mut self, cdb: &ClauseDB, vdb: &VarDB) {
        self.progress_cnt += 1;
        let nv = vdb.vars.len() - 1;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        let nlearnts = cdb.countf(Flag::LEARNT);
        let ncnfl = self.stats[Stat::Conflict];
        let nrestart = self.stats[Stat::Restart];
        println!(
            "c | {:>8}  {:>8} {:>8} | {:>7} {:>8} {:>8} |  {:>4}  {:>8} {:>7} {:>8} | {:>6.3} % |",
            nrestart,                              // restart
            self.stats[Stat::BlockRestart],        // blocked
            ncnfl / nrestart.max(1),               // average cfc (Conflict / Restart)
            nv - fixed - self.num_eliminated_vars, // alive vars
            cdb.count(true) - nlearnts,            // given clauses
            0,                                     // alive literals
            self.stats[Stat::Reduction],           // clause reduction
            nlearnts,                              // alive learnts
            self.stats[Stat::NumLBD2],             // learnts with LBD = 2
            ncnfl - nlearnts,                      // removed learnts
            (sum as f32) / (nv as f32) * 100.0,    // progress
        );
    }
    #[allow(dead_code)]
    fn dump_details(&mut self, cdb: &ClauseDB, elim: &Eliminator, vdb: &VarDB, mes: Option<&str>) {
        self.progress_cnt += 1;
        let msg = match mes {
            None => self.strategy.to_str(),
            Some(x) => x,
        };
        let nv = vdb.vars.len() - 1;
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
            self.stats[Stat::BlockRestart],
            self.stats[Stat::Restart],
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

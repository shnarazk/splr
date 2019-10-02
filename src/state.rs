use crate::clause::ClauseDB;
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::restart::RestartExecutor;
use crate::traits::*;
use crate::types::*;
use crate::var::{Var, VarDB};
use libc::{clock_gettime, timespec, CLOCK_PROCESS_CPUTIME_ID};
use std::cmp::Ordering;
use std::fmt;
use std::io::{stdout, Write};
use std::ops::{Index, IndexMut};
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
    Learnt,                // the number of learnt clauses (< Conflict)
    NoDecisionConflict,    // the number of 'no decision conflict'
    Propagation,           // the number of propagation
    Reduction,             // the number of reduction
    SatClauseElimination,  // the number of good old simplification
    ExhaustiveElimination, // the number of clause subsumption and variable elimination
    Assign,                // the number of assigned variables
    SolvedRecord,          // the last number of solved variables
    SumLBD,                // the sum of generated learnts' LBD
    NumBin,                // the number of binary clauses
    NumBinLearnt,          // the number of binary learnt clauses
    NumLBD2,               // the number of clauses which LBD is 2
    Stagnation,            // the number of stagnation
    EndOfStatIndex,        // Don't use this dummy.
}

impl Index<Stat> for [usize] {
    type Output = usize;
    fn index(&self, i: Stat) -> &usize {
        unsafe { self.get_unchecked(i as usize) }
    }
}

impl IndexMut<Stat> for [usize] {
    fn index_mut(&mut self, i: Stat) -> &mut usize {
        unsafe { self.get_unchecked_mut(i as usize) }
    }
}

/// Data storage for `Solver`
#[derive(Debug)]
pub struct State {
    pub root_level: usize,
    pub num_vars: usize,
    pub num_solved_vars: usize,
    pub num_eliminated_vars: usize,
    pub config: Config,
    pub rst: RestartExecutor,
    pub stats: [usize; Stat::EndOfStatIndex as usize], // statistics
    pub strategy: SearchStrategy,
    pub target: CNFDescription,
    pub use_chan_seok: bool,
    /// MISC
    pub ok: bool,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub model: Vec<Option<bool>>,
    pub conflicts: Vec<Lit>,
    pub new_learnt: Vec<Lit>,
    pub an_seen: Vec<bool>,
    pub last_asg: usize,
    pub last_dl: Vec<Lit>,
    pub lbd_temp: Vec<usize>,
    pub slack_duration: isize,
    pub stagnated: bool,
    pub start: SystemTime,
    pub time_limit: f64,
    pub record: ProgressRecord,
    pub use_progress: bool,
    pub progress_cnt: usize,
    pub progress_log: bool,
    pub development: Vec<(usize, f64, f64, f64, f64, f64)>,
}

impl Default for State {
    fn default() -> State {
        State {
            root_level: 0,
            num_vars: 0,
            num_solved_vars: 0,
            num_eliminated_vars: 0,
            config: Config::default(),
            rst: RestartExecutor::instantiate(&Config::default(), &CNFDescription::default()),
            stats: [0; Stat::EndOfStatIndex as usize],
            strategy: SearchStrategy::Initial,
            target: CNFDescription::default(),
            use_chan_seok: false,
            ok: true,
            b_lvl: Ema::new(5_000),
            c_lvl: Ema::new(5_000),
            model: Vec::new(),
            conflicts: Vec::new(),
            new_learnt: Vec::new(),
            an_seen: Vec::new(),
            last_asg: 0,
            last_dl: Vec::new(),
            lbd_temp: Vec::new(),
            slack_duration: 0,
            stagnated: false,
            start: SystemTime::now(),
            time_limit: 0.0,
            use_progress: true,
            progress_cnt: 0,
            progress_log: false,
            record: ProgressRecord::default(),
            development: Vec::new(),
        }
    }
}

macro_rules! im {
    ($format: expr, $record: expr, $key: expr, $val: expr) => {
        match ($val, $key) {
            (v, LogUsizeId::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $record[k];
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
        match ($val, $key) {
            (v, LogUsizeId::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $record[k];
                *ptr = v;
                format!($format, *ptr)
            }
        }
    };
}

macro_rules! fm {
    ($format: expr, $record: expr, $key: expr, $val: expr) => {
        match ($val, $key) {
            (v, LogF64Id::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $record[k];
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

#[allow(unused_macros)]
macro_rules! f {
    ($format: expr, $record: expr, $key: expr, $val: expr) => {
        match ($val, $key) {
            (v, LogF64Id::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $record[k];
                *ptr = v;
                format!($format, *ptr)
            }
        }
    };
}

impl Instantiate for State {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> State {
        let mut state = State::default();
        state.num_vars = cnf.num_of_variables;
        state.rst = RestartExecutor::instantiate(config, &cnf);
        state.progress_log = config.use_log;
        state.model = vec![None; cnf.num_of_variables + 1];
        state.an_seen = vec![false; cnf.num_of_variables + 1];
        state.lbd_temp = vec![0; cnf.num_of_variables + 1];
        state.target = cnf.clone();
        state.time_limit = config.timeout;
        state.config = config.clone();
        state
    }
}

impl StateIF for State {
    fn num_unsolved_vars(&self) -> usize {
        self.num_vars - self.num_solved_vars - self.num_eliminated_vars
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
    fn adapt_strategy(&mut self, cdb: &mut ClauseDB, vdb: &mut VarDB) {
        if self.config.without_adaptive_strategy || self.strategy != SearchStrategy::Initial {
            return;
        }
        let mut re_init = false;
        let decpc = self.stats[Stat::Decision] as f64 / self.stats[Stat::Conflict] as f64;
        if decpc <= 1.2 {
            self.strategy = SearchStrategy::LowDecisions;
            self.use_chan_seok = true;
            self.rst.cur_restart =
                (self.stats[Stat::Conflict] as f64 / cdb.next_reduction as f64 + 1.0) as usize;
            cdb.co_lbd_bound = 4;
            cdb.first_reduction = 2000;
            cdb.glureduce = true;
            cdb.inc_step = 0;
            cdb.next_reduction = 2000;
            re_init = true;
        }
        if self.stats[Stat::NoDecisionConflict] < 30_000 {
            if !self.config.without_deep_search {
                self.strategy = SearchStrategy::LowSuccesiveM;
            } else {
                self.strategy = SearchStrategy::LowSuccesiveLuby;
                self.rst.use_luby_restart = true;
                self.rst.luby_restart_factor = 100.0;
            }
            vdb.activity_decay = 0.999;
            vdb.activity_decay_max = 0.999;
        }
        if self.stats[Stat::NoDecisionConflict] > 54_400 {
            self.strategy = SearchStrategy::HighSuccesive;
            self.use_chan_seok = true;
            cdb.co_lbd_bound = 3;
            cdb.first_reduction = 30000;
            cdb.glureduce = true;
            vdb.activity_decay = 0.99;
            vdb.activity_decay_max = 0.99;
            // randomize_on_restarts = 1;
        }
        if self.stats[Stat::NumLBD2] - self.stats[Stat::NumBin] > 20_000 {
            self.strategy = SearchStrategy::ManyGlues;
            vdb.activity_decay = 0.91;
            vdb.activity_decay_max = 0.91;
        }
        if self.strategy == SearchStrategy::Initial {
            self.strategy = SearchStrategy::Generic;
            // self.config.without_deep_search = self.c_lvl.get().powf(2.0) < (self.num_unsolved_vars() as f64);
            return;
        }
        if self.use_chan_seok {
            cdb.make_permanent(re_init);
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
        let repeat = if 0 < self.config.dump_interval { 7 } else { 5 };
        for _i in 0..repeat {
            println!("                                                  ");
        }
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
    fn progress(&mut self, cdb: &ClauseDB, vars: &VarDB, mes: Option<&str>) {
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
        print!(
            "\x1B[{}A\x1B[1G",
            if 0 < self.config.dump_interval { 8 } else { 6 },
        );
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
            "\x1B[2K  Assignment|#rem:{}, #fix:{}, #elm:{}, prg%:{} ",
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
        println!(
            "\x1B[2K     Restart|#BLK:{}, #RST:{}, eASG:{}, eLBD:{} ",
            im!(
                "{:>9}",
                self.record,
                LogUsizeId::RestartBlock,
                self.stats[Stat::BlockRestart]
            ),
            im!(
                "{:>9}",
                self.record,
                LogUsizeId::Restart,
                self.stats[Stat::Restart]
            ),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::EmaAsg,
                self.rst.asg.trend()
            ),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::EmaLBD,
                self.rst.lbd.trend()
            ),
        );
        if 0 < self.config.dump_interval {
            println!(
                "\x1B[2K    Conflict|aLBD:{}, cnfl:{}, bjmp:{}, rpc%:{} ",
                fm!("{:>9.2}", self.record, LogF64Id::AveLBD, self.rst.lbd.get()),
                fm!("{:>9.2}", self.record, LogF64Id::CLevel, self.c_lvl.get()),
                fm!("{:>9.2}", self.record, LogF64Id::BLevel, self.b_lvl.get()),
                fm!(
                    "{:>9.4}",
                    self.record,
                    LogF64Id::End,
                    100.0 * self.stats[Stat::Restart] as f64 / self.stats[Stat::Conflict] as f64
                )
            );
            println!(
                "\x1B[2K   Clause DB|#rdc:{}, #sce:{} |blkR:{}, frcK:{} ",
                im!(
                    "{:>9}",
                    self.record,
                    LogUsizeId::Reduction,
                    self.stats[Stat::Reduction]
                ),
                im!(
                    "{:>9}",
                    self.record,
                    LogUsizeId::SatClauseElim,
                    self.stats[Stat::SatClauseElimination]
                ),
                fm!(
                    "{:>9.4}",
                    self.record,
                    LogF64Id::RestartBlkR,
                    self.rst.asg.threshold
                ),
                fm!(
                    "{:>9.4}",
                    self.record,
                    LogF64Id::RestartThrK,
                    self.rst.lbd.threshold
                ),
            );
        } else {
            self.record[LogF64Id::AveLBD] = self.rst.lbd.get();
            self.record[LogF64Id::CLevel] = self.c_lvl.get();
            self.record[LogF64Id::BLevel] = self.b_lvl.get();
            self.record[LogUsizeId::Reduction] = self.stats[Stat::Reduction];
            self.record[LogUsizeId::SatClauseElim] = self.stats[Stat::SatClauseElimination];
            self.record[LogF64Id::RestartBlkR] = self.rst.asg.threshold;
            self.record[LogF64Id::RestartThrK] = self.rst.lbd.threshold;
        }
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
    Restart,        // 11: restart_count: usize,
    Reduction,      // 12: reduction: usize,
    SatClauseElim,  // 13: simplification: usize,
    ExhaustiveElim, // 14: elimination: usize,
    Stagnation,     // 15: stagnation: usize,
    // ElimClauseQueue, // 16: elim_clause_queue: usize,
    // ElimVarQueue, // 17: elim_var_queue: usize,
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

impl Index<LogUsizeId> for ProgressRecord {
    type Output = usize;
    fn index(&self, i: LogUsizeId) -> &usize {
        &self.vali[i as usize]
    }
}

impl IndexMut<LogUsizeId> for ProgressRecord {
    fn index_mut(&mut self, i: LogUsizeId) -> &mut usize {
        &mut self.vali[i as usize]
    }
}

impl Index<LogF64Id> for ProgressRecord {
    type Output = f64;
    fn index(&self, i: LogF64Id) -> &f64 {
        &self.valf[i as usize]
    }
}

impl IndexMut<LogF64Id> for ProgressRecord {
    fn index_mut(&mut self, i: LogF64Id) -> &mut f64 {
        &mut self.valf[i as usize]
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
    fn dump(&mut self, cdb: &ClauseDB, vars: &VarDB) {
        self.progress_cnt += 1;
        let nv = vars.len() - 1;
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
            self.stats[Stat::BlockRestart],
            self.stats[Stat::Restart],
            self.rst.asg.get(),
            self.rst.lbd.get(),
            self.rst.lbd.get(),
            self.b_lvl.get(),
            self.c_lvl.get(),
            elim.clause_queue_len(),
            elim.var_queue_len(),
        );
    }
}

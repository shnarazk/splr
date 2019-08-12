use crate::clause::ClauseDB;
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::restart::{Ema, RestartExecutor};
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

const EMA_SLOW: usize = 8192; // 2 ^ 13; 2 ^ 15 = 32768
const EMA_FAST: usize = 64; // 2 ^ 6

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
    RestartByAsg,          // the number of restarts by assign stagnation
    RestartByFUP,          // the number of restarts by 1st unified (implication) point
    RestartByLuby,         // the number of Luby restart
    Learnt,                // the number of learnt clauses (< Conflict)
    NoDecisionConflict,    // the number of 'no decision conflict'
    Propagation,           // the number of propagation
    Reduction,             // the number of reduction
    SatClauseElimination,  // the number of good old simplification
    ExhaustiveElimination, // the number of clause subsumption and variable elimination
    Assign,                // the number of assigned variables
    NumBin,                // the number of binary clauses
    NumBinLearnt,          // the number of binary learnt clauses
    NumLBD2,               // the number of clauses which LBD is 2
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
    pub config: Config,
    pub target: CNFDescription,
    pub root_level: usize,
    pub num_vars: usize,
    pub num_solved_vars: usize,
    pub num_eliminated_vars: usize,
    /// STRATEGY
    pub use_adapt_strategy: bool,
    pub strategy: SearchStrategy,
    pub use_chan_seok: bool,
    pub co_lbd_bound: usize,
    pub lbd_frozen_clause: usize,
    /// CLAUSE/VARIABLE ACTIVITY
    pub cla_decay: f64,
    pub cla_inc: f64,
    pub var_inc: f64,
    /// CLAUSE REDUCTION
    pub cur_reduction: usize,
    pub first_reduction: usize,
    pub next_reduction: usize, // renamed from `nbclausesbeforereduce`
    pub glureduce: bool,
    pub cdb_inc: usize,
    pub cdb_inc_extra: usize,
    pub cdb_soft_limit: usize,
    pub ema_coeffs: (usize, usize),
    /// RESTART
    pub rst: RestartExecutor,
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
    pub elim_trigger: usize,
    /// MISC
    pub ok: bool,
    pub model: Vec<Lbool>,
    pub time_limit: f64,
    pub use_progress: bool,
    pub stats: [usize; Stat::EndOfStatIndex as usize], // statistics
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub conflicts: Vec<Lit>,
    pub new_learnt: Vec<Lit>,
    pub an_seen: Vec<bool>,
    pub last_dl: Vec<Lit>,
    pub progress_cnt: usize,
    pub progress_log: bool,
    pub start: SystemTime,
    pub record: ProgressRecord,
    pub development_history: Vec<(usize, f64, f64, f64, f64, f64, f64)>,
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
        let ema = (EMA_SLOW, EMA_FAST);
        State {
            config: Config::default(),
            target: CNFDescription::default(),
            root_level: 0,
            num_vars: 0,
            num_solved_vars: 0,
            num_eliminated_vars: 0,
            use_adapt_strategy: true,
            strategy: SearchStrategy::Initial,
            use_chan_seok: false,
            co_lbd_bound: 5,
            lbd_frozen_clause: 30,
            cla_decay: 0.999,
            cla_inc: 1.0,
            var_inc: 0.9,
            cur_reduction: 1,
            first_reduction: 1000,
            next_reduction: 1000,
            glureduce: true,
            cdb_inc: 300,
            cdb_inc_extra: 1000,
            cdb_soft_limit: 0, // 248_000_000
            ema_coeffs: ema,
            rst: RestartExecutor::new(1),
            use_elim: true,
            elim_eliminate_combination_limit: 80,
            elim_eliminate_grow_limit: 0, // 64
            elim_eliminate_loop_limit: 2_000_000,
            elim_subsume_literal_limit: 100,
            elim_subsume_loop_limit: 2_000_000,
            elim_trigger: 1,
            ok: true,
            model: Vec::new(),
            time_limit: 0.0,
            use_progress: true,
            stats: [0; Stat::EndOfStatIndex as usize],
            b_lvl: Ema::new(ema.0),
            c_lvl: Ema::new(ema.0),
            conflicts: Vec::new(),
            new_learnt: Vec::new(),
            an_seen: Vec::new(),
            last_dl: Vec::new(),
            progress_cnt: 0,
            progress_log: false,
            start: SystemTime::now(),
            record: ProgressRecord::default(),
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
        state.config = config.clone();
        state.num_vars = cnf.num_of_variables;
        state.use_adapt_strategy = !config.without_adaptive_strategy;
        state.cdb_soft_limit = config.clause_limit;
        state.rst = RestartExecutor::new(cnf.num_of_variables);
        state.elim_eliminate_grow_limit = config.elim_grow_limit;
        state.elim_subsume_literal_limit = config.elim_lit_limit;
        state.use_elim = !config.without_elim;
        state.model = vec![BOTTOM; cnf.num_of_variables + 1];
        state.time_limit = config.timeout;
        state.an_seen = vec![false; cnf.num_of_variables + 1];
        state.progress_log = config.use_log;
        state.target = cnf;
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
            self.cur_reduction =
                (self.stats[Stat::Conflict] as f64 / self.next_reduction as f64 + 1.0) as usize;
            self.first_reduction = 2000;
            self.next_reduction = 2000;
            self.cdb_inc = 0;
            re_init = true;
        }
        if self.stats[Stat::NoDecisionConflict] < 30_000 {
            self.strategy = SearchStrategy::LowSuccesiveLuby;
            self.rst.use_luby_restart = true;
            self.rst.luby.factor = 100.0;
            self.config.var_activity_decay = 0.999;
            self.config.var_activity_d_max = 0.999;
        }
        if self.stats[Stat::NoDecisionConflict] > 54_400 {
            self.strategy = SearchStrategy::HighSuccesive;
            self.use_chan_seok = true;
            self.glureduce = true;
            self.co_lbd_bound = 3;
            self.first_reduction = 30000;
            self.config.var_activity_decay = 0.99;
            self.config.var_activity_d_max = 0.99;
            // randomize_on_restarts = 1;
        }
        if self.stats[Stat::NumLBD2] - self.stats[Stat::NumBin] > 20_000 {
            self.strategy = SearchStrategy::ManyGlues;
            self.config.var_activity_decay = 0.91;
            self.config.var_activity_d_max = 0.91;
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
        let nv = self.num_vars;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        self.progress_cnt += 1;
        print!("\x1B[9A\x1B[1G");
        let ave_lbd = self.rst.lbd.sum / self.rst.lbd.num as f64;
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
        println!(
            "\x1B[2K  Assignment|#max:{}, #ave:{}, e-64:{}, trnd:{}  ",
            im!("{:>9.0}", self.record, LogUsizeId::AsgMax, self.rst.asg.max),
            fm!(
                "{:>9.0}",
                self.record,
                LogF64Id::ASGave,
                self.rst.asg.sum as f64 / self.rst.asg.num as f64
            ),
            fm!(
                "{:>9.0}",
                self.record,
                LogF64Id::ASGema,
                self.rst.asg.ema.get()
            ),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::ASGtrn,
                self.rst.asg.trend()
            ),
        );
        self.record[LogF64Id::VADecay] = vdb.activity_decay;
        println!(
            "\x1B[2K  Learnt LBD|#num:{}, #ave:{}, e-64:{}, trnd:{} ",
            // "\x1B[2K    Conflict|cnfl:{}, bjmp:{}, aLBD:{}, trnd:{} ",
            im!("{:>9.0}", self.record, LogUsizeId::Learnt, self.rst.lbd.num),
            fm!("{:>9.2}", self.record, LogF64Id::LBDave, ave_lbd),
            fm!(
                "{:>9.2}",
                self.record,
                LogF64Id::LBDema,
                self.rst.lbd.ema.get()
            ),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::LBDtrd,
                self.rst.lbd.trend()
            ),
        );
        println!(
            "\x1B[2K   First UIP|#sum:{}, rate:{}, e-64:{}, trnd:{} ",
            im!("{:>9}", self.record, LogUsizeId::FUPnum, self.rst.fup.sum),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::FUPave,
                self.rst.fup.sum as f64 / self.rst.fup.cnt as f64
            ),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::FUPdif,
                self.rst.fup.diff_ema.get()
            ),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::FUPtrd,
                self.rst.fup.trend()
            ),
        );
        println!(
            "\x1B[2K    Analysis|cLvl:{}, bLvl:{}, #rst:{}, run%:{} ",
            fm!("{:>9.2}", self.record, LogF64Id::CLevel, self.c_lvl.get()),
            fm!("{:>9.2}", self.record, LogF64Id::BLevel, self.b_lvl.get()),
            im!(
                "{:>9}",
                self.record,
                LogUsizeId::Restart,
                self.stats[Stat::Restart]
            ),
            fm!(
                "{:>9.4}",
                self.record,
                LogF64Id::RestartRatio,
                100.0 * self.rst.restart_ratio.get()
            ),
        );
        self.record[LogUsizeId::RestartByAsg] = self.stats[Stat::RestartByAsg];
        self.record[LogUsizeId::RestartByFUP] = self.stats[Stat::RestartByFUP];
        self.record[LogUsizeId::RestartByLuby] = self.stats[Stat::RestartByLuby];
        if let Some(m) = mes {
            println!("\x1B[2K    Strategy|mode: {}", m);
        } else {
            println!("\x1B[2K    Strategy|mode: {:#}", self.strategy);
        }
        self.flush("\x1B[2K");
        // update undisplayed fields
        self.record[LogUsizeId::Reduction] = self.stats[Stat::Reduction];
        self.record[LogUsizeId::SatClauseElim] = self.stats[Stat::SatClauseElimination];
        self.record[LogUsizeId::ExhaustiveElim] = self.stats[Stat::ExhaustiveElimination];
        self.record[LogUsizeId::Reduction] = self.stats[Stat::Reduction];
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
    Learnt,         // 10: learnt - binclause: usize
    Restart,        // 11: restart_count: usize,
    RestartByLuby,  // 12: restart_by_Luby restart
    RestartByAsg,   // 13: restart_by_assign_stagnation: usize,
    RestartByFUP,   // 14: restart_by_fup_stagnation: usize
    Reduction,      // 15: reduction: usize,
    SatClauseElim,  // 16: simplification: usize,
    ExhaustiveElim, // 17: elimination: usize,
    FUPnum,         // 18: the number of current fups
    AsgMax,         // 19:
    // ElimClauseQueue, // __: elim_clause_queue: usize,
    // ElimVarQueue, // __: elim_var_queue: usize,
    End,
}

/// Index for `f64` data, used in `ProgressRecord`
pub enum LogF64Id {
    Progress = 0, //  0: #remain / num_vars
    ASGave,       //  1: rst.asg.{sum / num}
    ASGema,       //  2: ema_asg.ema.get
    ASGtrn,       //  3: ema_asg.trend
    FUPinc,       //  4: ema_fup.diff_ema.slow: f64,
    FUPprg,       //  5: num_fup percentage: f64,
    FUPave,       //  6: rst.fup.{sum / num}
    FUPdif,       //  7: rst.fup.diff_ema.get
    FUPtrd,       //  8: rst.fup.trend
    LBDave,       //  9: rst.lbd.{sum / sum}
    LBDema,       // 10: rst.lbd.ema.get
    LBDtrd,       // 11: ema_lbd trend
    BLevel,       // 12: backjump_level
    CLevel,       // 13: conflict_level
    RestartRatio, // 14: rst.restart_ratio
    VADecay,      // 15: vdb.activity_decay
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
            0,                                     // blocked
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
            0,
            self.stats[Stat::Restart],
            self.rst.asg.ema.get(),
            self.rst.lbd.ema.get(),
            self.rst.lbd.ema.get(),
            self.b_lvl.get(),
            self.c_lvl.get(),
            elim.clause_queue_len(),
            elim.var_queue_len(),
        );
    }
}

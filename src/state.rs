/// Crate `state` is a collection of internal data.
use {
    crate::{
        clause::ClauseDBIF,
        config::Config,
        eliminator::EliminatorIF,
        propagator::PropagatorIF,
        restarter::{RestartIF, RestartMode},
        types::*,
        var::VarDBIF,
    },
    libc::{clock_gettime, timespec, CLOCK_PROCESS_CPUTIME_ID},
    std::{
        cmp::Ordering,
        fmt,
        io::{stdout, Write},
        ops::{Index, IndexMut},
        time::SystemTime,
    },
};

/// API for state/statistics management, providing `progress`.
pub trait StateIF {
    /// return the number of unsolved vars.
    fn num_unsolved_vars(&self) -> usize;
    /// return `true` if it is timed out.
    fn is_timeout(&self) -> bool;
    /// return elapsed time as a fraction.
    /// return None if something is wrong.
    fn elapsed(&self) -> Option<f64>;
    /// change heuristics based on stat data.
    fn select_strategy<A, C>(&mut self, asgs: &A, cdb: &C)
    where
        A: Export<(usize, usize, usize)> + PropagatorIF,
        C: Export<(usize, usize, usize, usize, usize, usize)> + ClauseDBIF;
    /// write a header of stat data to stdio.
    fn progress_header(&self);
    /// write stat data to stdio.
    fn progress<A, C, E, R, V>(
        &mut self,
        asgs: &A,
        cdb: &C,
        elim: &E,
        rst: &R,
        vdb: &V,
        mes: Option<&str>,
    ) where
        A: Export<(usize, usize, usize)> + PropagatorIF,
        C: Export<(usize, usize, usize, usize, usize, usize)> + ClauseDBIF,
        E: Export<(usize, usize)> + EliminatorIF,
        R: Export<(RestartMode, usize, f64, f64, f64)> + RestartIF,
        V: Export<(f64, f64)> + VarDBIF;
    /// write a short message to stdout.
    fn flush<S: AsRef<str>>(&self, mes: S);
}

/// A collection of named search heuristics.
#[derive(Debug, Eq, PartialEq)]
pub enum SearchStrategy {
    /// the initial search phase to determine a main strategy
    Initial,
    /// Non-Specific-Instance using a generic setting
    Generic,
    /// Many-Low-Level-Conflicts using Chan Seok heuristics
    LowDecisions,
    /// High-Successive-Conflicts using Chan Seok heuristics
    HighSuccesive,
    /// Low-Successive-Conflicts using Luby sequence
    LowSuccesive,
    /// Many-Glue-Clauses
    ManyGlues,
}

impl fmt::Display for SearchStrategy {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        if formatter.alternate() {
            write!(formatter, "{}", self.to_str())
        } else {
            let name = match self {
                SearchStrategy::Initial => "Initial",
                SearchStrategy::Generic => "Generic",
                SearchStrategy::LowDecisions => "LowDecs",
                SearchStrategy::HighSuccesive => "HighSucc",
                SearchStrategy::LowSuccesive => "LowSucc",
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
            // in the initial search phase to determine a main strategy
            SearchStrategy::Initial => "Initial search phase before a main strategy",
            // Non-Specific-Instance using a generic setting
            SearchStrategy::Generic => "Generic (using a generic parameter set)",
            // Many-Low-Level-Conflicts using Chan Seok heuristics
            SearchStrategy::LowDecisions => "LowDecisions (many conflicts at low levels)",
            // High-Successive-Conflicts using Chan Seok heuristics
            SearchStrategy::HighSuccesive => "HighSuccesiveConflict (long decision chains)",
            // Low-Successive-Conflicts-Luby w/ Luby sequence
            SearchStrategy::LowSuccesive => "LowSuccesive (successive conflicts)",
            // Many-Glue-Clauses
            SearchStrategy::ManyGlues => "ManyGlueClauses",
        }
    }
}

/// stat index.
#[derive(Clone, Eq, PartialEq)]
pub enum Stat {
    /// the number of decision
    Decision = 0,
    /// the number of 'no decision conflict'
    NoDecisionConflict,
    /// the last number of solved variables
    SolvedRecord,
    /// Don't use this dummy (setinel at the tail).
    EndOfStatIndex,
}

impl Index<Stat> for [usize] {
    type Output = usize;
    #[inline]
    fn index(&self, i: Stat) -> &usize {
        unsafe { self.get_unchecked(i as usize) }
    }
}

impl IndexMut<Stat> for [usize] {
    #[inline]
    fn index_mut(&mut self, i: Stat) -> &mut usize {
        unsafe { self.get_unchecked_mut(i as usize) }
    }
}

/// Data storage for `Solver`.
#[derive(Debug)]
pub struct State {
    pub root_level: DecisionLevel,
    pub num_vars: usize,
    pub num_solved_vars: usize,
    pub num_eliminated_vars: usize,
    pub config: Config,
    pub stats: [usize; Stat::EndOfStatIndex as usize], // statistics
    /// Tuple of current strategy and the number of conflicts at which the strategy is selected.
    pub strategy: (SearchStrategy, usize),
    pub target: CNFDescription,
    pub reflection_interval: usize,
    /// MISC
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub conflicts: Vec<Lit>,
    pub last_asg: usize,
    pub last_solved: usize,
    pub new_learnt: Vec<Lit>,
    pub progress_cnt: usize,
    pub record: ProgressRecord,
    pub start: SystemTime,
    pub time_limit: f64,
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
            stats: [0; Stat::EndOfStatIndex as usize],
            strategy: (SearchStrategy::Initial, 0),
            target: CNFDescription::default(),
            reflection_interval: 10_000,
            b_lvl: Ema::new(5_000),
            c_lvl: Ema::new(5_000),
            conflicts: Vec::new(),
            last_asg: 0,
            last_solved: 0,
            new_learnt: Vec::new(),
            progress_cnt: 0,
            record: ProgressRecord::default(),
            start: SystemTime::now(),
            time_limit: 0.0,
            development: Vec::new(),
        }
    }
}

impl Index<Stat> for State {
    type Output = usize;
    #[inline]
    fn index(&self, i: Stat) -> &usize {
        &self.stats[i as usize]
    }
}

impl IndexMut<Stat> for State {
    #[inline]
    fn index_mut(&mut self, i: Stat) -> &mut usize {
        &mut self.stats[i as usize]
    }
}

impl Instantiate for State {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> State {
        State {
            num_vars: cnf.num_of_variables,
            config: config.clone(),
            strategy: if config.without_adaptive_strategy {
                (SearchStrategy::Generic, 0)
            } else {
                (SearchStrategy::Initial, 0)
            },
            target: cnf.clone(),
            time_limit: config.timeout,
            ..State::default()
        }
    }
}

macro_rules! im {
    ($format: expr, $state: expr, $key: expr, $val: expr) => {
        match ($val, $key) {
            (v, LogUsizeId::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $state.record[k];
                if $state.config.quiet_mode {
                    *ptr = v;
                    format!($format, *ptr)
                } else if (v as f64) * 1.6 < *ptr as f64 {
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
    ($format: expr, $state: expr, $key: expr, $val: expr) => {
        match ($val, $key) {
            (v, LogUsizeId::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $state.record[k];
                *ptr = v;
                format!($format, *ptr)
            }
        }
    };
}

macro_rules! fm {
    ($format: expr, $state: expr, $key: expr, $val: expr) => {
        match ($val, $key) {
            (v, LogF64Id::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $state.record[k];
                if $state.config.quiet_mode {
                    *ptr = v;
                    format!($format, *ptr)
                } else if v * 1.6 < *ptr {
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
    ($format: expr, $state: expr, $key: expr, $val: expr) => {
        match ($val, $key) {
            (v, LogF64Id::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $state.record[k];
                *ptr = v;
                format!($format, *ptr)
            }
        }
    };
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
            Ok(e) => self.time_limit <= e.as_secs() as f64,
            Err(_) => false,
        }
    }
    fn elapsed(&self) -> Option<f64> {
        if self.time_limit == 0.0 {
            return Some(0.0);
        }
        match self.start.elapsed() {
            Ok(e) => Some(e.as_secs() as f64 / self.time_limit),
            Err(_) => None,
        }
    }
    fn select_strategy<A, C>(&mut self, asgs: &A, cdb: &C)
    where
        A: Export<(usize, usize, usize)> + PropagatorIF,
        C: Export<(usize, usize, usize, usize, usize, usize)> + ClauseDBIF,
    {
        if self.config.without_adaptive_strategy {
            return;
        }
        let (asgs_num_conflict, _num_propagation, _num_restart) = asgs.exports();
        let (_active, _bi_clause, cdb_num_bi_learnt, cdb_num_lbd2, _learnt, _reduction) =
            cdb.exports();
        debug_assert_eq!(self.strategy.0, SearchStrategy::Initial);
        self.strategy.0 = match () {
            _ if cdb_num_bi_learnt + 20_000 < cdb_num_lbd2 => SearchStrategy::ManyGlues,
            _ if self[Stat::Decision] as f64 <= 1.2 * asgs_num_conflict as f64 => {
                SearchStrategy::LowDecisions
            }
            _ if self[Stat::NoDecisionConflict] < 30_000 => SearchStrategy::LowSuccesive,
            _ if 54_400 < self[Stat::NoDecisionConflict] => SearchStrategy::HighSuccesive,
            _ => SearchStrategy::Generic,
        };
        self.strategy.1 = asgs_num_conflict;
    }
    fn progress_header(&self) {
        if self.config.quiet_mode {
            return;
        }
        if self.config.use_log {
            self.dump_header();
            return;
        }
        println!("{}", self);
        let repeat = 7;
        for _i in 0..repeat {
            println!("                                                  ");
        }
    }
    fn flush<S: AsRef<str>>(&self, mes: S) {
        if !self.config.quiet_mode && !self.config.use_log {
            if mes.as_ref().is_empty() {
                print!("\x1B[1G\x1B[K")
            } else {
                print!("{}", mes.as_ref());
            }
            stdout().flush().unwrap();
        }
    }
    /// `mes` should be shorter than or equal to 9, or 8 + a delimiter.
    #[allow(clippy::cognitive_complexity)]
    fn progress<A, C, E, R, V>(
        &mut self,
        asgs: &A,
        cdb: &C,
        elim: &E,
        rst: &R,
        vdb: &V,
        mes: Option<&str>,
    ) where
        A: Export<(usize, usize, usize)> + PropagatorIF,
        C: Export<(usize, usize, usize, usize, usize, usize)> + ClauseDBIF,
        E: Export<(usize, usize)> + EliminatorIF,
        R: Export<(RestartMode, usize, f64, f64, f64)> + RestartIF,
        V: Export<(f64, f64)> + VarDBIF,
    {
        //
        //## Gather stats from all modules
        //

        let (asgs_num_conflict, asgs_num_propagation, asgs_num_restart) = asgs.exports();

        let (
            cdb_num_active,
            cdb_num_bi_clause,
            _num_bi_learnt,
            cdb_num_lbd2,
            cdb_num_learnt,
            cdb_num_reduction,
        ) = cdb.exports();

        let (elim_num_full, _num_sat) = elim.exports();

        let (rst_mode, rst_num_block, rst_asg_trend, rst_lbd_get, rst_lbd_trend) = rst.exports();

        let (vdb_core_size, vdb_activity_decay) = vdb.exports();

        if self.config.quiet_mode {
            return;
        }
        if self.config.use_log {
            self.dump(asgs, cdb, rst, vdb);
            return;
        }
        let nv = self.target.num_of_variables;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;

        self.progress_cnt += 1;
        print!("\x1B[8A\x1B[1G");
        println!("\x1B[2K{}", self);
        println!(
            "\x1B[2K #conflict:{}, #decision:{}, #propagate:{} ",
            i!("{:>11}", self, LogUsizeId::Conflict, asgs_num_conflict),
            i!("{:>13}", self, LogUsizeId::Decision, self[Stat::Decision]),
            i!("{:>15}", self, LogUsizeId::Propagate, asgs_num_propagation),
        );
        println!(
            "\x1B[2K  Assignment|#rem:{}, #fix:{}, #elm:{}, prg%:{} ",
            im!("{:>9}", self, LogUsizeId::Remain, nv - sum),
            im!("{:>9}", self, LogUsizeId::Fixed, fixed),
            im!(
                "{:>9}",
                self,
                LogUsizeId::Eliminated,
                self.num_eliminated_vars
            ),
            fm!(
                "{:>9.4}",
                self,
                LogF64Id::Progress,
                (sum as f64) / (nv as f64) * 100.0
            ),
        );
        println!(
            "\x1B[2K      Clause|Remv:{}, LBD2:{}, Binc:{}, Perm:{} ",
            im!("{:>9}", self, LogUsizeId::Removable, cdb_num_learnt),
            im!("{:>9}", self, LogUsizeId::LBD2, cdb_num_lbd2),
            im!(
                "{:>9}",
                self,
                LogUsizeId::Binclause,
                cdb_num_bi_clause // cdb_num_bi_learnt
            ),
            im!(
                "{:>9}",
                self,
                LogUsizeId::Permanent,
                cdb_num_active - cdb_num_learnt
            ),
        );
        println!(
            "\x1B[2K {}|#BLK:{}, #RST:{}, tASG:{}, tLBD:{} ",
            match rst_mode {
                RestartMode::Dynamic => "    Restart",
                RestartMode::Luby => "\x1B[001m\x1B[035mLubyRestart\x1B[000m",
                RestartMode::Stabilize => "  \x1B[001m\x1B[030mStabilize\x1B[000m",
            },
            im!("{:>9}", self, LogUsizeId::RestartBlock, rst_num_block),
            im!("{:>9}", self, LogUsizeId::Restart, asgs_num_restart),
            fm!("{:>9.4}", self, LogF64Id::EmaAsg, rst_asg_trend),
            fm!("{:>9.4}", self, LogF64Id::EmaLBD, rst_lbd_trend),
        );
        println!(
            "\x1B[2K    Conflict|eLBD:{}, cnfl:{}, bjmp:{}, rpc%:{} ",
            fm!("{:>9.2}", self, LogF64Id::AveLBD, rst_lbd_get),
            fm!("{:>9.2}", self, LogF64Id::CLevel, self.c_lvl.get()),
            fm!("{:>9.2}", self, LogF64Id::BLevel, self.b_lvl.get()),
            fm!(
                "{:>9.4}",
                self,
                LogF64Id::End,
                100.0 * asgs_num_restart as f64 / asgs_num_conflict as f64
            )
        );
        println!(
            "\x1B[2K        misc|#rdc:{}, #elm:{}, core:{}, vdcy:{} ",
            im!("{:>9}", self, LogUsizeId::Reduction, cdb_num_reduction),
            im!("{:>9}", self, LogUsizeId::Elimination, elim_num_full),
            fm!("{:>9.0}", self, LogF64Id::CoreSize, vdb_core_size),
            format!("{:>9.4}", vdb_activity_decay),
        );
        if let Some(m) = mes {
            println!("\x1B[2K    Strategy|mode: {}", m);
        } else {
            println!("\x1B[2K    Strategy|mode: {:#}", self.strategy.0);
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
        let width = 59;
        let mut fname = self.target.pathname.to_string();
        if width <= fname.len() {
            fname.truncate(58 - vclen);
        }
        let fnlen = fname.len();
        if width < vclen + fnlen + 1 {
            write!(f, "{:<w$} |time:{:>9.2}", fname, tm, w = width)
        } else {
            write!(
                f,
                "{}{:>w$} |time:{:>9.2}",
                fname,
                &vc,
                tm,
                w = width - fnlen,
            )
        }
    }
}

impl Index<LogUsizeId> for State {
    type Output = usize;
    #[inline]
    fn index(&self, i: LogUsizeId) -> &Self::Output {
        &self.record[i]
    }
}

impl IndexMut<LogUsizeId> for State {
    #[inline]
    fn index_mut(&mut self, i: LogUsizeId) -> &mut Self::Output {
        &mut self.record[i]
    }
}

impl Index<LogF64Id> for State {
    type Output = f64;
    #[inline]
    fn index(&self, i: LogF64Id) -> &Self::Output {
        &self.record[i]
    }
}

impl IndexMut<LogF64Id> for State {
    #[inline]
    fn index_mut(&mut self, i: LogF64Id) -> &mut Self::Output {
        &mut self.record[i]
    }
}

/// Index for `Usize` data, used in `ProgressRecord`.
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
    Elimination,    // 13: full-featured elimination: usize,
    End,
}

/// Index for `f64` data, used in `ProgressRecord`.
pub enum LogF64Id {
    Progress = 0, //  0: progress: f64,
    EmaAsg,       //  1: ema_asg: f64,
    EmaLBD,       //  2: ema_lbd: f64,
    AveLBD,       //  3: ave_lbd: f64,
    BLevel,       //  4: backjump_level: f64,
    CLevel,       //  5: conflict_level: f64,
    CoreSize,     //  6: vdb.core_size.get: f64,
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
    #[inline]
    fn index(&self, i: LogUsizeId) -> &usize {
        &self.vali[i as usize]
    }
}

impl IndexMut<LogUsizeId> for ProgressRecord {
    #[inline]
    fn index_mut(&mut self, i: LogUsizeId) -> &mut usize {
        &mut self.vali[i as usize]
    }
}

impl Index<LogF64Id> for ProgressRecord {
    type Output = f64;
    #[inline]
    fn index(&self, i: LogF64Id) -> &f64 {
        &self.valf[i as usize]
    }
}

impl IndexMut<LogF64Id> for ProgressRecord {
    #[inline]
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
    fn dump<A, C, R, V>(&mut self, asgs: &A, cdb: &C, rst: &R, _vdb: &V)
    where
        A: Export<(usize, usize, usize)>,
        C: Export<(usize, usize, usize, usize, usize, usize)> + ClauseDBIF,
        R: Export<(RestartMode, usize, f64, f64, f64)> + RestartIF,
        V: Export<(f64, f64)>,
    {
        self.progress_cnt += 1;
        let nv = self.target.num_of_variables;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        let (asgs_num_conflict, _num_propagation, asgs_num_restart) = asgs.exports();
        let (
            cdb_num_active,
            _num_bi_clause,
            _num_bi_learnt,
            cdb_num_lbd2,
            cdb_num_learnt,
            cdb_num_reduction,
        ) = cdb.exports();
        let (_mode, rst_num_block, _asg_trend, _lbd_get, _lbd_trend) = rst.exports();
        println!(
            "c | {:>8}  {:>8} {:>8} | {:>7} {:>8} {:>8} |  {:>4}  {:>8} {:>7} {:>8} | {:>6.3} % |",
            asgs_num_restart,                            // restart
            rst_num_block,                               // blocked
            asgs_num_conflict / asgs_num_restart.max(1), // average cfc (Conflict / Restart)
            nv - fixed - self.num_eliminated_vars,       // alive vars
            cdb_num_active - cdb_num_learnt,             // given clauses
            0,                                           // alive literals
            cdb_num_reduction,                           // clause reduction
            cdb_num_learnt,                              // alive learnts
            cdb_num_lbd2,                                // learnts with LBD = 2
            asgs_num_conflict - cdb_num_learnt,          // removed learnts
            (sum as f32) / (nv as f32) * 100.0,          // progress
        );
    }
    #[allow(dead_code)]
    fn dump_details<A, C, E, R, V>(
        &mut self,
        asgs: &A,
        cdb: &C,
        _: &E,
        rst: &R,
        vdb: &V,
        mes: Option<&str>,
    ) where
        A: Export<(usize, usize, usize)> + PropagatorIF,
        C: Export<(usize, usize, usize, usize, usize, usize)> + ClauseDBIF,
        E: Export<(usize, usize, usize)> + EliminatorIF,
        R: Export<(RestartMode, usize, f64, f64, f64)> + RestartIF,
        V: Export<(f64, f64)> + VarDBIF,
    {
        self.progress_cnt += 1;
        let msg = match mes {
            None => self.strategy.0.to_str(),
            Some(x) => x,
        };
        let nv = vdb.len() - 1;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        let (_num_conflict, _num_propagation, asgs_num_restart) = asgs.exports();
        let (
            cdb_num_active,
            _num_bi_clause,
            _num_bi_learnt,
            _num_lbd2,
            cdb_num_learnt,
            _num_reduction,
        ) = cdb.exports();
        let (_mode, rst_num_block, rst_asg_trend, rst_lbd_get, rst_lbd_trend) = rst.exports();
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
            cdb_num_learnt,
            cdb_num_active,
            0,
            rst_num_block,
            asgs_num_restart,
            rst_asg_trend,
            rst_lbd_get,
            rst_lbd_trend,
            self.b_lvl.get(),
            self.c_lvl.get(),
            0, // elim.clause_queue_len(),
            0, // elim.var_queue_len(),
        );
    }
}

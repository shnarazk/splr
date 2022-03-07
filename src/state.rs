#[cfg(feature = "strategy_adaptation")]
use {crate::assign::AssignIF, std::cmp::Ordering};
/// Crate `state` is a collection of internal data.
use {
    crate::{
        assign, cdb, processor,
        solver::{self, SolverEvent, StageManager},
        types::*,
    },
    std::{
        fmt,
        io::{stdout, Write},
        ops::{Index, IndexMut},
        time::{Duration, Instant},
    },
};
#[cfg(not(feature = "strategy_adaptation"))]
const PROGRESS_REPORT_ROWS: usize = 8;
#[cfg(feature = "strategy_adaptation")]
const PROGRESS_REPORT_ROWS: usize = 9;

/// API for state/statistics management, providing [`progress`](`crate::state::StateIF::progress`).
pub trait StateIF {
    /// return `true` if it is timed out.
    fn is_timeout(&self) -> bool;
    /// return elapsed time as a fraction.
    /// return None if something is wrong.
    fn elapsed(&self) -> Option<f64>;

    #[cfg(feature = "strategy_adaptation")]
    /// change heuristics based on stat data.
    fn select_strategy<A, C>(&mut self, asg: &A, cdb: &C)
    where
        A: AssignIF,
        C: PropertyDereference<cdb::property::Tusize, usize>;

    /// write a header of stat data to stdio.
    fn progress_header(&mut self);
    /// write stat data to stdio.
    fn progress<A, C, E, R>(&mut self, asg: &A, cdb: &C, elim: &E, rst: &R)
    where
        A: PropertyDereference<assign::property::Tusize, usize>
            + PropertyReference<assign::property::TEma, EmaView>,
        C: PropertyDereference<cdb::property::Tusize, usize>
            + PropertyDereference<cdb::property::Tf64, f64>
            + PropertyReference<cdb::property::TEma, EmaView>,
        E: PropertyDereference<processor::property::Tusize, usize>,
        R: PropertyDereference<solver::restart::property::Tusize, usize>;
    /// write a short message to stdout.
    fn flush<S: AsRef<str>>(&self, mes: S);
    /// write a one-line message as log.
    fn log<S: AsRef<str>>(&mut self, tick: usize, mes: S);
}

#[cfg(feature = "strategy_adaptation")]
/// A collection of named search heuristics.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SearchStrategy {
    /// The initial search phase to determine a main strategy
    Initial,
    /// Non-Specific-Instance using a generic setting
    Generic,
    /// Many-Low-Level-Conflicts using Chan Seok heuristics
    LowDecisions,
    /// High-Successive-Conflicts using Chan Seok heuristics
    HighSuccessive,
    /// Low-Successive-Conflicts using Luby sequence
    LowSuccessive,
    /// Many-Glue-Clauses
    ManyGlues,
}

#[cfg(feature = "strategy_adaptation")]
impl fmt::Display for SearchStrategy {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        if formatter.alternate() {
            write!(formatter, "{}", self.to_str())
        } else {
            let name = match self {
                SearchStrategy::Initial => "Initial",
                SearchStrategy::Generic => "Generic",
                SearchStrategy::LowDecisions => "LowDecs",
                SearchStrategy::HighSuccessive => "HighSucc",
                SearchStrategy::LowSuccessive => "LowSucc",
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

#[cfg(feature = "strategy_adaptation")]
impl SearchStrategy {
    pub fn to_str(self) -> &'static str {
        match self {
            // in the initial search phase to determine a main strategy
            SearchStrategy::Initial => "Initial search phase before a main strategy",
            // Non-Specific-Instance using a generic setting
            SearchStrategy::Generic => "Generic (using a generic parameter set)",
            // Many-Low-Level-Conflicts using Chan Seok heuristics
            SearchStrategy::LowDecisions => "LowDecisions (many conflicts at low levels)",
            // High-Successive-Conflicts using Chan Seok heuristics
            SearchStrategy::HighSuccessive => "HighSuccessiveConflict (long decision chains)",
            // Low-Successive-Conflicts-Luby w/ Luby sequence
            SearchStrategy::LowSuccessive => "LowSuccessive (successive conflicts)",
            // Many-Glue-Clauses
            SearchStrategy::ManyGlues => "ManyGlueClauses",
        }
    }
}

/// stat index.
#[derive(Clone, Eq, PartialEq)]
pub enum Stat {
    /// the number of 'no decision conflict'
    NoDecisionConflict,
    /// the number of equivalency processor invocation
    NumProcessor,
    /// the number of vivification
    Vivification,
    /// the number of vivified (shrunk) clauses
    VivifiedClause,
    /// the number of vivified (asserted) vars
    VivifiedVar,
    /// don't use this dummy (sentinel at the tail).
    EndOfStatIndex,
}

impl Index<Stat> for [usize] {
    type Output = usize;
    #[inline]
    fn index(&self, i: Stat) -> &usize {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self[i as usize]
    }
}

impl IndexMut<Stat> for [usize] {
    #[inline]
    fn index_mut(&mut self, i: Stat) -> &mut usize {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.get_unchecked_mut(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self[i as usize]
    }
}

/// Data storage for [`Solver`](`crate::solver::Solver`).
#[derive(Clone, Debug)]
pub struct State {
    /// solver configuration
    pub config: Config,
    /// collection of statistics data
    pub stats: [usize; Stat::EndOfStatIndex as usize],
    /// StageManager
    pub stm: StageManager,

    #[cfg(feature = "strategy_adaptation")]
    /// tuple of current strategy and the number of conflicts at which the strategy is selected.
    pub strategy: (SearchStrategy, usize),

    /// problem description
    pub target: CNFDescription,
    /// strategy adjustment interval in conflict
    pub reflection_interval: usize,

    //
    //## MISC
    //
    /// EMA of backjump levels
    pub b_lvl: Ema,
    /// EMA of conflicting levels
    pub c_lvl: Ema,

    #[cfg(feature = "support_user_assumption")]
    /// hold conflicting user-defined *assumed* literals for UNSAT problems
    pub conflicts: Vec<Lit>,

    /// chronoBT threshold
    pub chrono_bt_threshold: DecisionLevel,
    /// hold the previous number of non-conflicting assignment
    pub last_asg: usize,
    /// working place to build learnt clauses
    pub new_learnt: Vec<Lit>,
    /// working place to store given clauses' ids which is used to derive a good learnt
    pub derive20: Vec<ClauseId>,
    /// `progress` invocation counter
    pub progress_cnt: usize,
    /// keep the previous statistics values
    pub record: ProgressRecord,
    /// start clock for timeout handling
    pub start: Instant,
    /// upper limit for timeout handling
    pub time_limit: f64,
    /// logging facility.
    log_messages: Vec<String>,
}

impl Default for State {
    fn default() -> State {
        State {
            config: Config::default(),
            stats: [0; Stat::EndOfStatIndex as usize],
            stm: StageManager::default(),

            #[cfg(feature = "strategy_adaptation")]
            strategy: (SearchStrategy::Initial, 0),

            target: CNFDescription::default(),
            reflection_interval: 10_000,

            b_lvl: Ema::new(5_000),
            c_lvl: Ema::new(5_000),

            #[cfg(feature = "support_user_assumption")]
            conflicts: Vec::new(),
            chrono_bt_threshold: 100,
            last_asg: 0,
            new_learnt: Vec::new(),
            derive20: Vec::new(),
            progress_cnt: 0,
            record: ProgressRecord::default(),
            start: Instant::now(),
            time_limit: 0.0,
            log_messages: Vec::new(),
        }
    }
}

impl Index<Stat> for State {
    type Output = usize;
    #[inline]
    fn index(&self, i: Stat) -> &usize {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.stats.get_unchecked(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.stats[i as usize]
    }
}

impl IndexMut<Stat> for State {
    #[inline]
    fn index_mut(&mut self, i: Stat) -> &mut usize {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.stats.get_unchecked_mut(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.stats[i as usize]
    }
}

impl Instantiate for State {
    fn instantiate(config: &Config, cnf: &CNFDescription) -> State {
        State {
            config: config.clone(),
            stm: StageManager::instantiate(config, cnf),

            #[cfg(feature = "strategy_adaptation")]
            strategy: (SearchStrategy::Initial, 0),

            target: cnf.clone(),
            time_limit: config.c_timeout,
            ..State::default()
        }
    }
    fn handle(&mut self, e: SolverEvent) {
        match e {
            SolverEvent::NewVar => {
                self.target.num_of_variables += 1;
            }
            SolverEvent::Assert(_) => (),
            SolverEvent::Conflict => (),
            SolverEvent::Eliminate(_) => (),
            SolverEvent::Instantiate => (),
            SolverEvent::Reinitialize => (),
            SolverEvent::Restart => (),
            SolverEvent::Stabilize(_) => (),

            #[cfg(feature = "clause_vivification")]
            SolverEvent::Vivify(_) => (),

            #[cfg(feature = "strategy_adaptation")]
            SolverEvent::Adapt(_, _) => (),
        }
    }
}

macro_rules! im {
    ($format: expr, $state: expr, $key: expr, $val: expr) => {
        match ($val, $key) {
            (v, LogUsizeId::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $state.record[k];
                if $state.config.no_color {
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
                    format!("\x1B[001m\x1B[036m{}\x1B[000m", format!($format, *ptr))
                } else if *ptr < v {
                    *ptr = v;
                    format!("\x1B[036m{}\x1B[000m", format!($format, *ptr))
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
                if $state.config.no_color {
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
                    format!("\x1B[001m\x1B[036m{}\x1B[000m", format!($format, *ptr))
                } else if *ptr < v {
                    *ptr = v;
                    format!("\x1B[036m{}\x1B[000m", format!($format, *ptr))
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
    fn is_timeout(&self) -> bool {
        Duration::from_secs(self.config.c_timeout as u64) < self.start.elapsed()
    }
    fn elapsed(&self) -> Option<f64> {
        Some(
            self.start.elapsed().as_secs_f64()
                / Duration::from_secs(self.config.c_timeout as u64).as_secs_f64(),
        )
    }
    #[cfg(feature = "strategy_adaptation")]
    fn select_strategy<A, C>(&mut self, asg: &A, cdb: &C)
    where
        A: AssignIF,
        C: PropertyDereference<cdb::property::Tusize, usize>,
    {
        let asg_num_conflict = asg.derefer(assign::property::Tusize::NumConflict);
        let asg_num_decision = asg.derefer(assign::property::Tusize::NumDecision);
        let cdb_num_bi_learnt = cdb.derefer(cdb::property::Tusize::NumBiLearnt);
        let cdb_num_lbd2 = cdb.derefer(cdb::property::Tusize::NumLBD2);

        debug_assert_eq!(self.strategy.0, SearchStrategy::Initial);
        self.strategy.0 = match () {
            _ if cdb_num_bi_learnt + 20_000 < cdb_num_lbd2 => SearchStrategy::ManyGlues,
            _ if asg_num_decision as f64 <= 1.2 * asg_num_conflict as f64 => {
                SearchStrategy::LowDecisions
            }
            _ if self[Stat::NoDecisionConflict] < 15_000 => SearchStrategy::LowSuccessive,
            _ if 54_400 < self[Stat::NoDecisionConflict] => SearchStrategy::HighSuccessive,
            _ => SearchStrategy::Generic,
        };
        self.strategy.1 = asg_num_conflict;
    }
    fn progress_header(&mut self) {
        if !self.config.splr_interface || self.config.quiet_mode {
            return;
        }
        if self.config.use_log {
            self.dump_header();
            return;
        }
        if 0 == self.progress_cnt {
            self.progress_cnt = 1;
            println!("{}", self);

            //## PROGRESS REPORT ROWS
            for _i in 0..PROGRESS_REPORT_ROWS - 1 {
                println!("                                                  ");
            }
        }
    }
    fn flush<S: AsRef<str>>(&self, mes: S) {
        if self.config.splr_interface && !self.config.quiet_mode && !self.config.use_log {
            if mes.as_ref().is_empty() {
                print!("\x1B[1G\x1B[K")
            } else {
                print!("{}", mes.as_ref());
            }
            stdout().flush().unwrap();
        }
    }
    fn log<S: AsRef<str>>(&mut self, tick: usize, mes: S) {
        if self.config.splr_interface && !self.config.quiet_mode && !self.config.use_log {
            self.log_messages
                .insert(0, format!("[{:>10}] {}", tick, mes.as_ref()));
        }
    }
    /// `mes` should be shorter than or equal to 9, or 8 + a delimiter.
    #[allow(clippy::cognitive_complexity)]
    fn progress<A, C, E, R>(&mut self, asg: &A, cdb: &C, elim: &E, rst: &R)
    where
        A: PropertyDereference<assign::property::Tusize, usize>
            + PropertyReference<assign::property::TEma, EmaView>,
        C: PropertyDereference<cdb::property::Tusize, usize>
            + PropertyDereference<cdb::property::Tf64, f64>
            + PropertyReference<cdb::property::TEma, EmaView>,
        E: PropertyDereference<processor::property::Tusize, usize>,
        R: PropertyDereference<solver::restart::property::Tusize, usize>,
    {
        if !self.config.splr_interface || self.config.quiet_mode {
            self.log_messages.clear();
            self.record_stats(asg, cdb, elim, rst);
            return;
        }

        //
        //## Gather stats from all modules
        //
        let asg_num_vars = asg.derefer(assign::property::Tusize::NumVar);
        let asg_num_asserted_vars = asg.derefer(assign::property::Tusize::NumAssertedVar);
        let asg_num_eliminated_vars = asg.derefer(assign::property::Tusize::NumEliminatedVar);
        let asg_num_unasserted_vars = asg.derefer(assign::property::Tusize::NumUnassertedVar);
        let asg_num_unreachables = asg.derefer(assign::property::Tusize::NumUnreachableVar);
        let rate = (asg_num_asserted_vars + asg_num_eliminated_vars) as f64 / asg_num_vars as f64;
        let asg_num_conflict = asg.derefer(assign::property::Tusize::NumConflict);
        let asg_num_decision = asg.derefer(assign::property::Tusize::NumDecision);
        let asg_num_propagation = asg.derefer(assign::property::Tusize::NumPropagation);

        let asg_dpc_ema = asg.refer(assign::property::TEma::DecisionPerConflict);
        let asg_ppc_ema = asg.refer(assign::property::TEma::PropagationPerConflict);
        let asg_cpr_ema = asg.refer(assign::property::TEma::ConflictPerRestart);

        let cdb_num_clause = cdb.derefer(cdb::property::Tusize::NumClause);
        let cdb_num_bi_clause = cdb.derefer(cdb::property::Tusize::NumBiClause);
        let cdb_num_lbd2 = cdb.derefer(cdb::property::Tusize::NumLBD2);
        let cdb_num_learnt = cdb.derefer(cdb::property::Tusize::NumLearnt);
        let cdb_lbd_of_dp: f64 = cdb.derefer(cdb::property::Tf64::LiteralBlockEntanglement);

        let elim_num_full = elim.derefer(processor::property::Tusize::NumFullElimination);
        let elim_num_sub = elim.derefer(processor::property::Tusize::NumSubsumedClause);

        let rst_num_blk: usize = rst.derefer(solver::restart::property::Tusize::NumBlock);
        let rst_num_rst: usize = rst.derefer(solver::restart::property::Tusize::NumRestart);
        let rst_int_scl: usize = self.stm.current_scale();
        let rst_int_scl_max: usize = self.stm.max_scale();
        let rst_asg: &EmaView = asg.refer(assign::property::TEma::AssignRate);
        let rst_lbd: &EmaView = cdb.refer(cdb::property::TEma::LBD);

        if self.config.use_log {
            self.dump(asg, cdb, rst);
            return;
        }
        self.progress_cnt += 1;
        // print!("\x1B[9A\x1B[1G");
        print!("\x1B[");
        print!("{}", PROGRESS_REPORT_ROWS);
        print!("A\x1B[1G");

        if self.config.show_journal {
            while let Some(m) = self.log_messages.pop() {
                if self.config.no_color {
                    println!("{}", m);
                } else {
                    println!("\x1B[2K\x1B[000m\x1B[034m{}\x1B[000m", m);
                }
            }
        } else {
            self.log_messages.clear();
        }
        println!("\x1B[2K{}", self);
        println!(
            "\x1B[2K #conflict:{}, #decision:{}, #propagate:{}",
            i!("{:>11}", self, LogUsizeId::NumConflict, asg_num_conflict),
            i!("{:>13}", self, LogUsizeId::NumDecision, asg_num_decision),
            i!(
                "{:>15}",
                self,
                LogUsizeId::NumPropagate,
                asg_num_propagation
            ),
        );
        println!(
            "\x1B[2K  Assignment|#rem:{}, #fix:{}, #elm:{}, prg%:{}",
            im!(
                "{:>9}",
                self,
                LogUsizeId::RemainingVar,
                asg_num_unasserted_vars
            ),
            im!(
                "{:>9}",
                self,
                LogUsizeId::AssertedVar,
                asg_num_asserted_vars
            ),
            im!(
                "{:>9}",
                self,
                LogUsizeId::EliminatedVar,
                asg_num_eliminated_vars
            ),
            fm!("{:>9.4}", self, LogF64Id::Progress, rate * 100.0),
        );
        println!(
            "\x1B[2K      Clause|Remv:{}, LBD2:{}, BinC:{}, Perm:{}",
            im!("{:>9}", self, LogUsizeId::RemovableClause, cdb_num_learnt),
            im!("{:>9}", self, LogUsizeId::LBD2Clause, cdb_num_lbd2),
            im!(
                "{:>9}",
                self,
                LogUsizeId::BiClause,
                cdb_num_bi_clause // cdb_num_bi_learnt
            ),
            im!(
                "{:>9}",
                self,
                LogUsizeId::PermanentClause,
                cdb_num_clause - cdb_num_learnt
            ),
        );
        println!(
            "\x1B[2K     Restart|#BLK:{}, #RST:{}, *scl:{}, sclM:{}",
            im!("{:>9}", self, LogUsizeId::RestartBlock, rst_num_blk),
            im!("{:>9}", self, LogUsizeId::Restart, rst_num_rst),
            im!("{:>9}", self, LogUsizeId::RestartIntervalScale, rst_int_scl),
            im!(
                "{:>9}",
                self,
                LogUsizeId::RestartIntervalScaleMax,
                rst_int_scl_max
            ),
        );
        println!(
            "\x1B[2K         LBD|trnd:{}, avrg:{}, depG:{}, /dpc:{}",
            fm!("{:>9.4}", self, LogF64Id::TrendLBD, rst_lbd.trend()),
            fm!("{:>9.4}", self, LogF64Id::EmaLBD, rst_lbd.get_fast()),
            fm!(
                "{:>9.4}",
                self,
                LogF64Id::LiteralBlockEntanglement,
                cdb_lbd_of_dp
            ),
            fm!(
                "{:>9.2}",
                self,
                LogF64Id::DecisionPerConflict,
                asg_dpc_ema.get()
            ),
        );
        println!(
            "\x1B[2K    Conflict|tASG:{}, cLvl:{}, bLvl:{}, /ppc:{}",
            fm!("{:>9.4}", self, LogF64Id::TrendASG, rst_asg.trend()),
            fm!("{:>9.2}", self, LogF64Id::CLevel, self.c_lvl.get()),
            fm!("{:>9.2}", self, LogF64Id::BLevel, self.b_lvl.get()),
            fm!(
                "{:>9.2}",
                self,
                LogF64Id::PropagationPerConflict,
                asg_ppc_ema.get()
            ),
        );
        println!(
            "\x1B[2K        misc|vivC:{}, subC:{}, core:{}, /cpr:{}",
            im!(
                "{:>9}",
                self,
                LogUsizeId::VivifiedClause,
                self[Stat::VivifiedClause]
            ),
            im!("{:>9}", self, LogUsizeId::SubsumedClause, elim_num_sub),
            im!(
                "{:>9}",
                self,
                LogUsizeId::UnreachableCore,
                if asg_num_unreachables == 0 {
                    self[LogUsizeId::UnreachableCore]
                } else {
                    asg_num_unreachables
                }
            ),
            fm!(
                "{:>9.2}",
                self,
                LogF64Id::ConflictPerRestart,
                asg_cpr_ema.get()
            )
        );
        self[LogUsizeId::NumProcessor] = self[Stat::NumProcessor];
        self[LogUsizeId::Simplify] = elim_num_full;
        self[LogUsizeId::Stabilize] = self.stm.current_stage();
        self[LogUsizeId::StabilizationCycle] = self.stm.current_cycle();
        self[LogUsizeId::Vivify] = self[Stat::Vivification];

        #[cfg(feature = "strategy_adaptation")]
        {
            println!("\x1B[2K    Strategy|mode: {:#}", self.strategy.0);
        }
        self.flush("");
    }
}

impl State {
    #[allow(clippy::cognitive_complexity)]
    fn record_stats<A, C, E, R>(&mut self, asg: &A, cdb: &C, elim: &E, rst: &R)
    where
        A: PropertyDereference<assign::property::Tusize, usize>
            + PropertyReference<assign::property::TEma, EmaView>,
        C: PropertyDereference<cdb::property::Tusize, usize>
            + PropertyDereference<cdb::property::Tf64, f64>
            + PropertyReference<cdb::property::TEma, EmaView>,
        E: PropertyDereference<processor::property::Tusize, usize>,
        R: PropertyDereference<solver::restart::property::Tusize, usize>,
    {
        self[LogUsizeId::NumConflict] = asg.derefer(assign::property::Tusize::NumConflict);
        self[LogUsizeId::NumDecision] = asg.derefer(assign::property::Tusize::NumDecision);
        self[LogUsizeId::NumPropagate] = asg.derefer(assign::property::Tusize::NumPropagation);
        self[LogUsizeId::RemainingVar] = asg.derefer(assign::property::Tusize::NumUnassertedVar);
        self[LogUsizeId::AssertedVar] = asg.derefer(assign::property::Tusize::NumAssertedVar);
        self[LogUsizeId::EliminatedVar] = asg.derefer(assign::property::Tusize::NumEliminatedVar);
        self[LogF64Id::Progress] = 100.0
            * (self[LogUsizeId::AssertedVar]
                + asg.derefer(assign::property::Tusize::NumEliminatedVar)) as f64
            / asg.derefer(assign::property::Tusize::NumVar) as f64;
        self[LogUsizeId::RemovableClause] = cdb.derefer(cdb::property::Tusize::NumLearnt);
        self[LogUsizeId::LBD2Clause] = cdb.derefer(cdb::property::Tusize::NumLBD2);
        self[LogUsizeId::BiClause] = cdb.derefer(cdb::property::Tusize::NumBiClause);
        self[LogUsizeId::PermanentClause] =
            cdb.derefer(cdb::property::Tusize::NumClause) - self[LogUsizeId::RemovableClause];
        self[LogUsizeId::RestartBlock] = rst.derefer(solver::restart::property::Tusize::NumBlock);
        self[LogUsizeId::Restart] = rst.derefer(solver::restart::property::Tusize::NumRestart);
        self[LogUsizeId::RestartIntervalScale] = self.stm.current_scale();
        self[LogUsizeId::RestartIntervalScaleMax] = self.stm.max_scale();
        self[LogUsizeId::Stabilize] = self.stm.current_stage();
        self[LogUsizeId::StabilizationCycle] = self.stm.current_cycle();
        self[LogUsizeId::NumProcessor] = self[Stat::NumProcessor];
        self[LogUsizeId::Simplify] = elim.derefer(processor::property::Tusize::NumFullElimination);

        self[LogUsizeId::SubsumedClause] =
            elim.derefer(processor::property::Tusize::NumSubsumedClause);
        self[LogUsizeId::VivifiedClause] = self[Stat::VivifiedClause];
        self[LogUsizeId::VivifiedVar] = self[Stat::VivifiedVar];
        self[LogUsizeId::Vivify] = self[Stat::Vivification];
        let rst_lbd: &EmaView = cdb.refer(cdb::property::TEma::LBD);
        self[LogF64Id::EmaLBD] = rst_lbd.get_fast();
        self[LogF64Id::TrendLBD] = rst_lbd.trend();

        self[LogF64Id::LiteralBlockEntanglement] =
            cdb.derefer(cdb::property::Tf64::LiteralBlockEntanglement);
        self[LogF64Id::DecisionPerConflict] =
            asg.refer(assign::property::TEma::DecisionPerConflict).get();

        self[LogF64Id::TrendASG] = asg.refer(assign::property::TEma::AssignRate).trend();
        self[LogF64Id::CLevel] = self.c_lvl.get();
        self[LogF64Id::BLevel] = self.b_lvl.get();
        self[LogF64Id::PropagationPerConflict] = asg
            .refer(assign::property::TEma::PropagationPerConflict)
            .get();
        {
            let core = asg.derefer(assign::property::Tusize::NumUnreachableVar);
            if 0 < core {
                self[LogUsizeId::UnreachableCore] = core;
            }
        }
        self[LogF64Id::ConflictPerRestart] =
            asg.refer(assign::property::TEma::ConflictPerRestart).get();
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tm: f64 = (self.start.elapsed().as_millis() as f64) / 1_000.0;
        let vc = format!(
            "{},{}",
            self.target.num_of_variables, self.target.num_of_clauses,
        );
        let vclen = vc.len();
        let width = 59;
        let mut fname = match &self.target.pathname {
            CNFIndicator::Void => "(no cnf)".to_string(),
            CNFIndicator::File(f) => f.to_string(),
            CNFIndicator::LitVec(n) => format!("(embedded {} element vector)", n),
        };
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
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.record.vali.get_unchecked(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.record.vali[i as usize]
    }
}

impl IndexMut<LogUsizeId> for State {
    #[inline]
    fn index_mut(&mut self, i: LogUsizeId) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.record.vali.get_unchecked_mut(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.record.vali[i as usize]
    }
}

impl Index<LogF64Id> for State {
    type Output = f64;
    #[inline]
    fn index(&self, i: LogF64Id) -> &Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.record.valf.get_unchecked(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.record.valf[i as usize]
    }
}

impl IndexMut<LogF64Id> for State {
    #[inline]
    fn index_mut(&mut self, i: LogF64Id) -> &mut Self::Output {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.record.valf.get_unchecked_mut(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.record.valf[i as usize]
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
            "   #init,    #remain,#asserted,#elim,total%,,#learnt,  \
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
    fn dump<A, C, R>(&mut self, asg: &A, cdb: &C, rst: &R)
    where
        A: PropertyDereference<assign::property::Tusize, usize>,
        C: PropertyDereference<cdb::property::Tusize, usize>,
        R: PropertyDereference<solver::restart::property::Tusize, usize>,
    {
        self.progress_cnt += 1;
        let asg_num_vars = asg.derefer(assign::property::Tusize::NumVar);
        let asg_num_asserted_vars = asg.derefer(assign::property::Tusize::NumAssertedVar);
        let asg_num_eliminated_vars = asg.derefer(assign::property::Tusize::NumEliminatedVar);
        let asg_num_unasserted_vars = asg.derefer(assign::property::Tusize::NumUnassertedVar);
        let rate = (asg_num_asserted_vars + asg_num_eliminated_vars) as f64 / asg_num_vars as f64;
        let asg_num_conflict = asg.derefer(assign::property::Tusize::NumConflict);
        let asg_num_restart = asg.derefer(assign::property::Tusize::NumRestart);
        let cdb_num_clause = cdb.derefer(cdb::property::Tusize::NumClause);
        let cdb_num_lbd2 = cdb.derefer(cdb::property::Tusize::NumLBD2);
        let cdb_num_learnt = cdb.derefer(cdb::property::Tusize::NumLearnt);
        let cdb_num_reduction = cdb.derefer(cdb::property::Tusize::NumReduction);
        let rst_num_block = rst.derefer(solver::restart::property::Tusize::NumBlock);
        println!(
            "c | {:>8}  {:>8} {:>8} | {:>7} {:>8} {:>8} |  {:>4}  {:>8} {:>7} {:>8} | {:>6.3} % |",
            asg_num_restart,                           // restart
            rst_num_block,                             // blocked
            asg_num_conflict / asg_num_restart.max(1), // average cfc (Conflict / Restart)
            asg_num_unasserted_vars,                   // alive vars
            cdb_num_clause - cdb_num_learnt,           // given clauses
            0,                                         // alive literals
            cdb_num_reduction,                         // clause reduction
            cdb_num_learnt,                            // alive learnts
            cdb_num_lbd2,                              // learnts with LBD = 2
            asg_num_conflict - cdb_num_learnt,         // removed learnts
            rate * 100.0,                              // progress
        );
    }
    #[allow(dead_code)]
    fn dump_details<'r, A, C, E, R, V>(&mut self, asg: &A, cdb: &C, rst: &'r R)
    where
        A: PropertyDereference<assign::property::Tusize, usize>
            + PropertyReference<assign::property::TEma, EmaView>,
        C: PropertyDereference<cdb::property::Tusize, usize>
            + PropertyReference<cdb::property::TEma, EmaView>,
        R: PropertyDereference<solver::restart::property::Tusize, usize>,
    {
        self.progress_cnt += 1;
        let asg_num_vars = asg.derefer(assign::property::Tusize::NumVar);
        let asg_num_asserted_vars = asg.derefer(assign::property::Tusize::NumAssertedVar);
        let asg_num_eliminated_vars = asg.derefer(assign::property::Tusize::NumEliminatedVar);
        let asg_num_unasserted_vars = asg.derefer(assign::property::Tusize::NumUnassertedVar);
        let rate = (asg_num_asserted_vars + asg_num_eliminated_vars) as f64 / asg_num_vars as f64;
        let asg_num_restart = asg.derefer(assign::property::Tusize::NumRestart);
        let cdb_num_clause = cdb.derefer(cdb::property::Tusize::NumClause);
        let cdb_num_learnt = cdb.derefer(cdb::property::Tusize::NumLearnt);
        let rst_num_block = rst.derefer(solver::restart::property::Tusize::NumBlock);
        let rst_asg = asg.refer(assign::property::TEma::AssignRate);
        let rst_lbd = cdb.refer(cdb::property::TEma::LBD);

        println!(
            "{:>3},{:>7},{:>7},{:>7},{:>6.3},,{:>7},{:>7},\
             {:>7},,{:>5},{:>5},{:>6.2},{:>6.2},,{:>7.2},{:>8.2},{:>8.2},,\
             {:>6},{:>6}",
            self.progress_cnt,
            asg_num_unasserted_vars,
            asg_num_asserted_vars,
            asg_num_eliminated_vars,
            rate * 100.0,
            cdb_num_learnt,
            cdb_num_clause,
            0,
            rst_num_block,
            asg_num_restart,
            rst_asg.trend(),
            rst_lbd.get(),
            rst_lbd.trend(),
            self.b_lvl.get(),
            self.c_lvl.get(),
            0, // elim.clause_queue_len(),
            0, // elim.var_queue_len(),
        );
    }
}

/// Index for `Usize` data, used in [`ProgressRecord`](`crate::state::ProgressRecord`).
#[derive(Clone, Copy, Debug)]
pub enum LogUsizeId {
    //
    //## primary stats
    //
    NumConflict = 0,
    NumPropagate,
    NumDecision,

    //
    //## vars
    //
    RemainingVar,
    AssertedVar,
    EliminatedVar,
    UnreachableCore,

    //
    //## clause
    //
    RemovableClause,
    LBD2Clause,
    BiClause,
    PermanentClause,

    //
    //## stabilization, staging and restart
    //
    Restart,
    RestartBlock,
    RestartCancel,
    RestartStabilize,
    RestartIntervalScale,
    RestartIntervalScaleMax,
    Stabilize,
    StabilizationCycle,

    //
    //## pre(in)-processor
    //
    NumProcessor,
    Simplify,
    SubsumedClause,
    VivifiedClause,
    VivifiedVar,
    Vivify,

    // the sentinel
    End,
}

/// Index for `f64` data, used in [`ProgressRecord`](`crate::state::ProgressRecord`).
#[derive(Clone, Copy, Debug)]
pub enum LogF64Id {
    Progress = 0,
    EmaASG,
    EmaCCC,
    EmaLBD,
    EmaMLD,
    TrendASG,
    TrendLBD,
    BLevel,
    CLevel,
    DecisionPerConflict,
    ConflictPerRestart,
    PropagationPerConflict,
    LiteralBlockEntanglement,
    End,
}

/// Record of old stats.
#[derive(Clone, Debug)]
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
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.vali.get_unchecked(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.vali[i as usize]
    }
}

impl IndexMut<LogUsizeId> for ProgressRecord {
    #[inline]
    fn index_mut(&mut self, i: LogUsizeId) -> &mut usize {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.vali.get_unchecked_mut(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.vali[i as usize]
    }
}

impl Index<LogF64Id> for ProgressRecord {
    type Output = f64;
    #[inline]
    fn index(&self, i: LogF64Id) -> &f64 {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.valf.get_unchecked(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &self.valf[i as usize]
    }
}

impl IndexMut<LogF64Id> for ProgressRecord {
    #[inline]
    fn index_mut(&mut self, i: LogF64Id) -> &mut f64 {
        #[cfg(feature = "unsafe_access")]
        unsafe {
            self.valf.get_unchecked_mut(i as usize)
        }
        #[cfg(not(feature = "unsafe_access"))]
        &mut self.valf[i as usize]
    }
}

pub mod property {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Tusize {
        /// the number of 'no decision conflict'
        NumNoDecisionConflict,
        // the number for processor invocations
        NumProcessor,
        /// the number of vivification
        Vivification,
        /// the number of vivified (shrunk) clauses
        VivifiedClause,
        /// the number of vivified (asserted) vars
        VivifiedVar,

        //
        //## from stageManager
        //
        NumCycle,
        NumStage,
        IntervalScale,
        IntervalScaleMax,
    }

    pub const USIZES: [Tusize; 9] = [
        Tusize::NumNoDecisionConflict,
        Tusize::NumProcessor,
        Tusize::Vivification,
        Tusize::VivifiedClause,
        Tusize::VivifiedVar,
        Tusize::NumCycle,
        Tusize::NumStage,
        Tusize::IntervalScale,
        Tusize::IntervalScaleMax,
    ];

    impl PropertyDereference<Tusize, usize> for State {
        #[inline]
        fn derefer(&self, k: Tusize) -> usize {
            match k {
                Tusize::NumNoDecisionConflict => self[Stat::NoDecisionConflict],
                Tusize::NumProcessor => self[Stat::NumProcessor],
                Tusize::Vivification => self[Stat::Vivification],
                Tusize::VivifiedClause => self[Stat::VivifiedClause],
                Tusize::VivifiedVar => self[Stat::VivifiedVar],
                Tusize::NumCycle => self.stm.current_cycle(),
                Tusize::NumStage => self.stm.current_stage(),
                Tusize::IntervalScale => self.stm.current_scale(),
                Tusize::IntervalScaleMax => self.stm.max_scale(),
            }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum TEma {
        BackjumpLevel,
        ConflictLevel,
    }

    pub const EMAS: [TEma; 2] = [TEma::BackjumpLevel, TEma::ConflictLevel];

    impl PropertyReference<TEma, EmaView> for State {
        #[inline]
        fn refer(&self, k: TEma) -> &EmaView {
            match k {
                TEma::BackjumpLevel => &self.b_lvl.as_view(),
                TEma::ConflictLevel => &self.c_lvl.as_view(),
            }
        }
    }
}

#[cfg(feature = "strategy_adaptation")]
use {crate::cdb::ClauseDBIF, std::cmp::Ordering};
/// Crate `state` is a collection of internal data.
use {
    crate::{
        assign::{AssignIF, VarSelectIF},
        solver::{RestartIF, RestartMode, RestarterEMAs, SolverEvent},
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
        A: Export<(usize, usize, usize, f64), ()>,
        C: ClauseDBIF + Export<(usize, usize, usize, usize, usize, usize), bool>;

    /// write a header of stat data to stdio.
    fn progress_header(&mut self);
    /// write stat data to stdio.
    fn progress<'r, A, C, E, R>(&mut self, asg: &A, cdb: &C, elim: &E, rst: &'r R)
    where
        A: AssignIF + VarSelectIF + Export<(usize, usize, usize, f64), ()>,
        C: Export<(usize, usize, usize, usize, usize, usize), bool>,
        E: Export<(usize, usize, f64), ()>,
        R: RestartIF + ExportBox<'r, RestarterEMAs<'r>>;
    /// write a short message to stdout.
    fn flush<S: AsRef<str>>(&self, mes: S);
    /// write a one-line message as log.
    fn log<S: AsRef<str>>(&mut self, tick: usize, mes: S);
}

/// Phase saving modes.
#[derive(Debug, Eq, PartialEq)]
pub enum StagingTarget {
    /// select some targets cyclicly.
    AutoSelect,
    /// use best phases with some unsettled vars
    Best(usize),
    /// unstage all vars.
    Clear,
    /// choose vars in core
    Core,
    ///
    LastAssigned,
    /// select random vars.
    Random,

    #[cfg(feature = "explore_timestamp")]
    /// seek unchecked vars.
    Explore,
}

impl fmt::Display for StagingTarget {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(
            formatter,
            "{}",
            match self {
                StagingTarget::AutoSelect => "StageMode",
                StagingTarget::Best(_) => "StageMode_top",
                StagingTarget::Clear => "StageMode_Clear",
                StagingTarget::Core => "StageMode_Core",
                StagingTarget::LastAssigned => "StageMode_LA",
                StagingTarget::Random => "Stage_Random",

                #[cfg(feature = "explore_timestamp")]
                StagingTarget::Explore => "StageMode_Exp",
            }
        )
    }
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
    /// the number of decision
    Decision,
    /// the number of 'no decision conflict'
    NoDecisionConflict,
    /// the number of vivification
    Vivification,
    /// the number of vivified (asserted) vars
    VivifiedVar,
    /// don't use this dummy (sentinel at the tail).
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

/// Data storage for [`Solver`](`crate::solver::Solver`).
#[derive(Debug)]
pub struct State {
    /// solver configuration
    pub config: Config,
    /// collection of statistics data
    pub stats: [usize; Stat::EndOfStatIndex as usize],

    #[cfg(feature = "strategy_adaptation")]
    /// tuple of current strategy and the number of conflicts at which the strategy is selected.
    pub strategy: (SearchStrategy, usize),

    /// problem description
    pub target: CNFDescription,
    /// strategy adjustment interval in conflict
    pub reflection_interval: usize,
    /// time to execute vivification
    pub to_vivify: f64,
    /// loop limit of vivification loop
    pub vivify_thr: usize,
    //
    //## MISC
    //
    /// EMA of backjump levels
    pub b_lvl: Ema,
    /// EMA of conflicting levels
    pub c_lvl: Ema,
    /// hold conflicting literals for UNSAT problems
    pub conflicts: Vec<Lit>,
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

            #[cfg(feature = "strategy_adaptation")]
            strategy: (SearchStrategy::Initial, 0),

            target: CNFDescription::default(),
            reflection_interval: 10_000,
            to_vivify: 0.0,
            vivify_thr: 0,
            b_lvl: Ema::new(5_000),
            c_lvl: Ema::new(5_000),
            conflicts: Vec::new(),
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
            config: config.clone(),

            #[cfg(feature = "strategy_adaptation")]
            strategy: if config.use_adaptive() {
                (SearchStrategy::Initial, 0)
            } else {
                (SearchStrategy::Generic, 0)
            },

            vivify_thr: config.viv_thr,
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
            SolverEvent::Stabilize((_, _)) => (),
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
        A: Export<(usize, usize, usize, f64), ()>,
        C: ClauseDBIF + Export<(usize, usize, usize, usize, usize, usize), bool>,
    {
        if !self.config.use_adaptive() {
            return;
        }
        let (asg_num_conflict, _num_propagation, _num_restart, _) = asg.exports();
        let (_active, _bi_clause, cdb_num_bi_learnt, cdb_num_lbd2, _learnt, _reduction) =
            cdb.exports();
        debug_assert_eq!(self.strategy.0, SearchStrategy::Initial);
        self.strategy.0 = match () {
            _ if cdb_num_bi_learnt + 20_000 < cdb_num_lbd2 => SearchStrategy::ManyGlues,
            _ if self[Stat::Decision] as f64 <= 1.2 * asg_num_conflict as f64 => {
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
    fn progress<'r, A, C, E, R>(&mut self, asg: &A, cdb: &C, elim: &E, rst: &'r R)
    where
        A: AssignIF + VarSelectIF + Export<(usize, usize, usize, f64), ()>,
        C: Export<(usize, usize, usize, usize, usize, usize), bool>,
        E: Export<(usize, usize, f64), ()>,
        R: RestartIF + ExportBox<'r, RestarterEMAs<'r>>,
    {
        if !self.config.splr_interface || self.config.quiet_mode {
            return;
        }

        //
        //## Gather stats from all modules
        //
        let (
            asg_num_vars,
            asg_num_asserted_vars,
            asg_num_eliminated_vars,
            asg_num_unasserted_vars,
            asg_unreachables,
        ) = asg.var_stats();
        let rate = (asg_num_asserted_vars + asg_num_eliminated_vars) as f64 / asg_num_vars as f64;
        let (asg_num_conflict, asg_num_propagation, asg_num_restart, _asg_act_dcy) = asg.exports();

        let (cdb_num_active, cdb_num_biclause, _num_bl, cdb_num_lbd2, cdb_num_learnt, _cdb_nr) =
            cdb.exports();

        let (elim_num_full, _num_sat, _elim_to_simplify) = elim.exports();

        let rst_mode = rst.mode().0;

        let (rst_num_blk, rst_num_rst, rst_num_span, rst_num_cycle, _stb_lspan) = rst.exports();
        // let rst_num_stb = rst.mode().1;

        #[cfg(not(feature = "progress_ACC"))]
        let (rst_asg, rst_lbd) = *rst.exports_box();

        #[cfg(feature = "progress_ACC")]
        let (_rst_acc, rst_asg, rst_lbd) = *rst.exports_box();

        if self.config.use_log {
            self.dump(asg, cdb, rst);
            return;
        }
        self.progress_cnt += 1;
        // print!("\x1B[9A\x1B[1G");
        print!("\x1B[");
        print!("{}", PROGRESS_REPORT_ROWS);
        print!("A\x1B[1G");

        while let Some(m) = self.log_messages.pop() {
            if self.config.no_color {
                println!("{}", m);
            } else {
                println!("\x1B[2K\x1B[000m\x1B[034m{}\x1B[000m", m);
            }
        }
        println!("\x1B[2K{}", self);
        println!(
            "\x1B[2K #conflict:{}, #decision:{}, #propagate:{}",
            i!("{:>11}", self, LogUsizeId::NumConflict, asg_num_conflict),
            i!(
                "{:>13}",
                self,
                LogUsizeId::NumDecision,
                self[Stat::Decision]
            ),
            i!(
                "{:>15}",
                self,
                LogUsizeId::NumPropagate,
                asg_num_propagation
            ),
        );
        println!(
            "\x1B[2K  Assignment|#rem:{}, #ass:{}, #elm:{}, prg%:{}",
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
            "\x1B[2K      Clause|Remv:{}, LBD2:{}, Binc:{}, Perm:{}",
            im!("{:>9}", self, LogUsizeId::RemovableClause, cdb_num_learnt),
            im!("{:>9}", self, LogUsizeId::LBD2Clause, cdb_num_lbd2),
            im!(
                "{:>9}",
                self,
                LogUsizeId::Binclause,
                cdb_num_biclause // cdb_num_bi_learnt
            ),
            im!(
                "{:>9}",
                self,
                LogUsizeId::PermanentClause,
                cdb_num_active - cdb_num_learnt
            ),
        );
        println!(
            "\x1B[2K {}|#BLK:{}, #RST:{}, #ion:{}, Lspn:{}",
            match rst_mode {
                RestartMode::Dynamic => "    Restart",
                RestartMode::Luby if self.config.no_color => "LubyRestart",
                RestartMode::Luby => "\x1B[001m\x1B[035mLubyRestart\x1B[000m",
                RestartMode::Stabilize if self.config.no_color => "  Stabilize",
                RestartMode::Stabilize => "  \x1B[001m\x1B[036mStabilize\x1B[000m",
            },
            im!("{:>9}", self, LogUsizeId::RestartBlock, rst_num_blk),
            im!("{:>9}", self, LogUsizeId::Restart, rst_num_rst),
            im!("{:>9}", self, LogUsizeId::NumIon, {
                #[cfg(not(feature = "staging"))]
                {
                    0
                }
                #[cfg(feature = "staging")]
                {
                    asg.num_staging_cands()
                }
            }),
            im!("{:>9}", self, LogUsizeId::LubySpan, rst_num_span),
        );
        self[LogUsizeId::LubyCycle] = rst_num_cycle;
        println!(
            "\x1B[2K         EMA|tLBD:{}, tASG:{}, core:{}, /dpc:{}",
            fm!("{:>9.4}", self, LogF64Id::TrendLBD, rst_lbd.trend()),
            fm!("{:>9.4}", self, LogF64Id::TrendASG, rst_asg.trend()),
            im!("{:>9}", self, LogUsizeId::UnreachableCore, asg_unreachables),
            fm!(
                "{:>9.2}",
                self,
                LogF64Id::DecisionPerConflict,
                self[Stat::Decision] as f64 / asg_num_conflict as f64
            ),
        );
        println!(
            "\x1B[2K    Conflict|eLBD:{}, cnfl:{}, bjmp:{}, /ppc:{}",
            fm!("{:>9.2}", self, LogF64Id::EmaLBD, rst_lbd.get()),
            fm!("{:>9.2}", self, LogF64Id::CLevel, self.c_lvl.get()),
            fm!("{:>9.2}", self, LogF64Id::BLevel, self.b_lvl.get()),
            fm!(
                "{:>9.2}",
                self,
                LogF64Id::PropagationPerConflict,
                asg_num_propagation as f64 / asg_num_conflict as f64
            ),
        );
        println!(
            "\x1B[2K        misc|elim:{}, cviv:{}, #vbv:{}, /cpr:{}",
            im!("{:>9}", self, LogUsizeId::Simplify, elim_num_full),
            im!("{:>9}", self, LogUsizeId::Vivify, self[Stat::Vivification]),
            im!(
                "{:>9}",
                self,
                LogUsizeId::VivifiedVar,
                self[Stat::VivifiedVar]
            ),
            fm!(
                "{:>9.2}",
                self,
                LogF64Id::ConflictPerRestart,
                asg_num_conflict as f64 / asg_num_restart as f64
            )
        );
        #[cfg(feature = "strategy_adaptation")]
        {
            println!("\x1B[2K    Strategy|mode: {:#}", self.strategy.0);
        }
        self.flush("");
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
        A: AssignIF + Export<(usize, usize, usize, f64), ()>,
        C: Export<(usize, usize, usize, usize, usize, usize), bool>,
        R: RestartIF,
    {
        self.progress_cnt += 1;
        let (
            asg_num_vars,
            asg_num_asserted_vars,
            asg_num_eliminated_vars,
            asg_num_unasserted_vars,
            _,
        ) = asg.var_stats();
        let rate = (asg_num_asserted_vars + asg_num_eliminated_vars) as f64 / asg_num_vars as f64;
        let (asg_num_conflict, _num_propagation, asg_num_restart, _) = asg.exports();
        let (
            cdb_num_active,
            _num_bi_clause,
            _num_bi_learnt,
            cdb_num_lbd2,
            cdb_num_learnt,
            cdb_num_reduction,
        ) = cdb.exports();
        let rst_num_block = {
            let e = rst.exports();
            e.0 + e.2
        };
        println!(
            "c | {:>8}  {:>8} {:>8} | {:>7} {:>8} {:>8} |  {:>4}  {:>8} {:>7} {:>8} | {:>6.3} % |",
            asg_num_restart,                           // restart
            rst_num_block,                             // blocked
            asg_num_conflict / asg_num_restart.max(1), // average cfc (Conflict / Restart)
            asg_num_unasserted_vars,                   // alive vars
            cdb_num_active - cdb_num_learnt,           // given clauses
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
        A: AssignIF + Export<(usize, usize, usize, f64), ()>,
        C: Export<(usize, usize, usize, usize, usize, usize), bool>,
        R: RestartIF + ExportBox<'r, RestarterEMAs<'r>>,
    {
        self.progress_cnt += 1;
        let (
            asg_num_vars,
            asg_num_asserted_vars,
            asg_num_eliminated_vars,
            asg_num_unasserted_vars,
            _,
        ) = asg.var_stats();
        let rate = (asg_num_asserted_vars + asg_num_eliminated_vars) as f64 / asg_num_vars as f64;
        let (_num_conflict, _num_propagation, asg_num_restart, _) = asg.exports();
        let (
            cdb_num_active,
            _num_bi_clause,
            _num_bi_learnt,
            _num_lbd2,
            cdb_num_learnt,
            _num_reduction,
        ) = cdb.exports();
        let rst_num_block = {
            let e = rst.exports();
            e.0 + e.2
        };

        #[cfg(not(feature = "progress_ACC"))]
        let (rst_asg, rst_lbd) = *rst.exports_box();

        #[cfg(feature = "progress_ACC")]
        let (_, rst_asg, rst_lbd) = *rst.exports_box();

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
            cdb_num_active,
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
    Binclause,
    PermanentClause,

    //
    //## stabilization, staging and restart
    //
    LubyCycle,
    LubySpan,
    NumIon,
    Restart,
    RestartBlock,
    RestartCancel,
    RestartStabilize,

    //
    //## pre-in processor
    //
    Simplify,
    Stabilize,
    Vivify,
    VivifiedVar,

    // the sentinel
    End,
}

/// Index for `f64` data, used in [`ProgressRecord`](`crate::state::ProgressRecord`).
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

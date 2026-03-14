/// Module `state` is a collection of internal data.
#[cfg(feature = "platform_wasm")]
use instant::{Duration, Instant};
#[cfg(not(feature = "platform_wasm"))]
use std::time::{Duration, Instant};
use {
    crate::{
        assign, cdb,
        cdb::ClauseDBIF,
        solver::{RestartManager, SolverEvent, StageManager},
        types::*,
    },
    std::{
        fmt,
        io::{Write, stdout},
        ops::{Index, IndexMut},
    },
};
const PROGRESS_REPORT_ROWS: usize = 7;
const CDB_HEATMAP_ROWS: usize = 7;

/// API for state/statistics management, providing [`progress`](`crate::state::StateIF::progress`).
pub trait StateIF {
    /// return `true` if it is timed out.
    fn is_timeout(&self) -> bool;
    /// return elapsed time as a fraction.
    /// return None if something is wrong.
    fn elapsed(&self) -> Option<f64>;
    /// write a header of stat data to stdio.
    fn progress_header(&mut self);
    /// write stat data to stdio.
    fn progress<A, C>(&mut self, asg: &A, cdb: &C)
    where
        A: PropertyDereference<assign::property::Tusize, usize>
            + PropertyDereference<assign::property::Tf64, f64>
            + PropertyReference<assign::property::TEma, EmaView>,
        C: ClauseDBIF
            + PropertyDereference<cdb::property::Tusize, usize>
            + PropertyDereference<cdb::property::Tf64, f64>
            + PropertyReference<cdb::property::TEma, EmaView>;
    /// write a short message to stdout.
    fn flush<S: AsRef<str>>(&self, mes: S);
    /// write a one-line message as log.
    fn log<S: AsRef<str>>(&mut self, tick: Option<(Option<usize>, Option<usize>, usize)>, mes: S);
}

/// stat index.
#[derive(Clone, Eq, PartialEq)]
pub enum Stat {
    Restart,
    /// the number of vivification
    Vivification,
    /// the number of vivified (shrunk) clauses
    VivifiedClause,
    /// the number of vivified (asserted) vars
    VivifiedVar,
    /// the number of invocations of simplify
    Simplify,
    /// the number of subsumed clause by processor
    SubsumedClause,
    /// for SLS
    SLS,
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
    /// the problem.
    pub cnf: CNFDescription,
    /// collection of statistics data
    pub stats: [usize; Stat::EndOfStatIndex as usize],
    // Restart
    pub restart: RestartManager,
    /// StageManager
    pub stm: StageManager,
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
    /// EMA of backtrack level drift caused by chrono_BT or BT_deepen
    pub bt_drift_average: Ema,
    /// EMA of c_lbd - b_lbd, or Exploration vs. Eploitation
    pub e_mode: Ema2,
    pub e_mode_threshold: f64,
    pub exploration_rate_ema: Ema,

    #[cfg(feature = "support_user_assumption")]
    /// hold conflicting user-defined *assumed* literals for UNSAT problems
    pub conflicts: Vec<Lit>,

    #[cfg(feature = "chrono_BT")]
    /// chronoBT threshold
    pub chrono_bt_threshold: DecisionLevel,
    pub num_chrono_bt: usize,

    /// hold the previous number of non-conflicting assignment
    pub last_asg: usize,
    /// working place to build learnt clauses
    pub new_learnt: Vec<Lit>,
    /// `progress` invocation counter
    pub progress_cnt: usize,
    /// keep the previous statistics values
    pub record: ProgressRecord,
    /// progress of SLS
    pub sls_index: usize,
    /// start clock for timeout handling
    pub start: Instant,
    /// upper limit for timeout handling
    pub time_limit: f64,
    /// logging facility.
    log_messages: Vec<String>,
    progress_report_rows: usize,
}

impl Default for State {
    fn default() -> State {
        State {
            config: Config::default(),
            cnf: CNFDescription::default(),
            stats: [0; Stat::EndOfStatIndex as usize],
            restart: RestartManager::default(),
            stm: StageManager::default(),
            target: CNFDescription::default(),
            reflection_interval: 10_000,

            b_lvl: Ema::new(5_000),
            c_lvl: Ema::new(5_000),
            bt_drift_average: Ema::new(1000),
            e_mode: Ema2::new(40).with_slow(4_000).with_value(10.0),
            e_mode_threshold: 1.20,
            exploration_rate_ema: Ema::new(1000),

            #[cfg(feature = "support_user_assumption")]
            conflicts: Vec::new(),

            #[cfg(feature = "chrono_BT")]
            chrono_bt_threshold: 100,
            num_chrono_bt: 0,

            last_asg: 0,
            new_learnt: Vec::new(),
            progress_cnt: 0,
            record: ProgressRecord::default(),
            sls_index: 0,
            start: Instant::now(),
            time_limit: 0.0,
            log_messages: Vec::new(),
            progress_report_rows: PROGRESS_REPORT_ROWS,
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
            cnf: cnf.clone(),
            restart: RestartManager::instantiate(config, cnf),
            stm: StageManager::instantiate(config, cnf),
            target: cnf.clone(),
            time_limit: config.c_timeout,
            progress_report_rows: PROGRESS_REPORT_ROWS
                + CDB_HEATMAP_ROWS * (config.show_cdb_heatmap as usize),
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
            SolverEvent::Restart => {
                self[Stat::Restart] += 1;
                self.restart.handle(SolverEvent::Restart);
            }
            SolverEvent::Stage(_) => (),

            #[cfg(feature = "clause_vivification")]
            SolverEvent::Vivify(_) => (),
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
    ($format: expr, $state: expr, $key: expr, $val: expr, $threshold: expr) => {
        match ($val, $key) {
            (v, LogUsizeId::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $state.record[k];
                if $state.config.no_color {
                    *ptr = v;
                    format!($format, *ptr)
                } else if v < $threshold {
                    *ptr = v;
                    format!("\x1B[031m{}\x1B[000m", format!($format, *ptr))
                } else if $threshold < v {
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
    ($format: expr, $state: expr, $key: expr, $val: expr, $threshold: expr) => {
        match ($val, $key) {
            (v, LogF64Id::End) => format!($format, v),
            (v, k) => {
                let ptr = &mut $state.record[k];
                if $state.config.no_color {
                    *ptr = v;
                    format!($format, *ptr)
                } else if v + $threshold < *ptr {
                    if v * 1.6 < *ptr {
                        *ptr = v;
                        format!("\x1B[001m\x1B[031m{}\x1B[000m", format!($format, *ptr))
                    } else {
                        *ptr = v;
                        format!("\x1B[031m{}\x1B[000m", format!($format, *ptr))
                    }
                } else if *ptr + $threshold < v {
                    if *ptr * 1.6 < v {
                        *ptr = v;
                        format!("\x1B[001m\x1B[036m{}\x1B[000m", format!($format, *ptr))
                    } else {
                        *ptr = v;
                        format!("\x1B[036m{}\x1B[000m", format!($format, *ptr))
                    }
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
    fn progress_header(&mut self) {
        if !self.config.splr_interface || self.config.quiet_mode {
            return;
        }
        if 0 == self.progress_cnt {
            self.progress_cnt = 1;
            println!("{self}");

            //## PROGRESS REPORT ROWS
            for _i in 0..self.progress_report_rows - 1 {
                println!("                                                  ");
            }
        }
    }
    fn flush<S: AsRef<str>>(&self, mes: S) {
        if self.config.splr_interface && !self.config.quiet_mode {
            if mes.as_ref().is_empty() {
                print!("\x1B[1G\x1B[K")
            } else {
                print!("{}", mes.as_ref());
            }
            stdout().flush().unwrap();
        }
    }
    fn log<S: AsRef<str>>(&mut self, tick: Option<(Option<usize>, Option<usize>, usize)>, mes: S) {
        if self.config.splr_interface && !self.config.quiet_mode {
            self.log_messages.insert(
                0,
                match tick {
                    Some((Some(seg), Some(cyc), stg)) => {
                        format!("stage({:>2},{:>4},{:>5}): {}", seg, cyc, stg, mes.as_ref())
                    }
                    Some((None, Some(cyc), stg)) => {
                        format!("stage(  ,{:>4},{:>5}): {}", cyc, stg, mes.as_ref())
                    }
                    Some((None, None, stg)) => {
                        format!("stage(  ,    ,{:>5}): {}", stg, mes.as_ref())
                    }
                    Some(_) => unreachable!(),
                    None => format!("### {}", mes.as_ref()),
                },
            );
        }
    }
    /// `mes` should be shorter than or equal to 9, or 8 + a delimiter.
    #[allow(clippy::cognitive_complexity)]
    fn progress<A, C>(&mut self, asg: &A, cdb: &C)
    where
        A: PropertyDereference<assign::property::Tusize, usize>
            + PropertyDereference<assign::property::Tf64, f64>
            + PropertyReference<assign::property::TEma, EmaView>,
        C: ClauseDBIF
            + PropertyDereference<cdb::property::Tusize, usize>
            + PropertyDereference<cdb::property::Tf64, f64>
            + PropertyReference<cdb::property::TEma, EmaView>,
    {
        if !self.config.splr_interface || self.config.quiet_mode {
            self.log_messages.clear();
            self.record_stats(asg, cdb);
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
        // let asg_cwss: f64 = asg.derefer(assign::property::Tf64::CurrentWorkingSetSize);
        let asg_dpc_ema = asg.refer(assign::property::TEma::DecisionPerConflict);
        let asg_ppc_ema = asg.refer(assign::property::TEma::PropagationPerConflict);
        let asg_cpr_ema = asg.refer(assign::property::TEma::ConflictPerRestart);

        let cdb_num_clause = cdb.derefer(cdb::property::Tusize::NumClause);
        let cdb_num_bi_clause = cdb.derefer(cdb::property::Tusize::NumBiClause);
        let cdb_num_lbd2 = cdb.derefer(cdb::property::Tusize::NumLBD2);
        let cdb_num_learnt = cdb.derefer(cdb::property::Tusize::NumLearnt);
        let cdb_lb_ent: f64 = cdb.derefer(cdb::property::Tf64::LiteralBlockEntanglement);
        let rst_num_rst: usize = self[Stat::Restart];
        let rst_asg: &EmaView = asg.refer(assign::property::TEma::AssignRate);
        let rst_lbd: &EmaView = cdb.refer(cdb::property::TEma::LBD);
        let rst_eng: f64 = self.restart.penetration_energy_charged;
        let stg_segment: usize = self.stm.current_segment();

        self.progress_cnt += 1;
        // print!("\x1B[9A\x1B[1G");
        print!("\x1B[");
        print!("{}", self.progress_report_rows);
        print!("A\x1B[1G");

        if self.config.show_journal {
            while let Some(m) = self.log_messages.pop() {
                if self.config.no_color {
                    println!("{m}");
                } else {
                    println!("\x1B[2K\x1B[000m\x1B[034m{m}\x1B[000m");
                }
            }
        } else {
            self.log_messages.clear();
        }
        println!("\x1B[2K{self}");
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
        self[LogUsizeId::StageSegment] = stg_segment;
        self[LogF64Id::RestartEnergy] = rst_eng;
        self[LogF64Id::TrendASG] = rst_asg.trend();
        println!(
            "\x1B[2K    Conflict|entg:{}, cLvl:{}, bLvl:{}, /cpr:{}",
            fm!(
                "{:>9.2}",
                self,
                LogF64Id::LiteralBlockEntanglement,
                cdb_lb_ent,
                0.01
            ),
            fm!("{:>9.2}", self, LogF64Id::CLevel, self.c_lvl.get(), 0.01),
            fm!("{:>9.2}", self, LogF64Id::BLevel, self.b_lvl.get(), 0.01),
            fm!(
                "{:>9.2}",
                self,
                LogF64Id::ConflictPerRestart,
                asg_cpr_ema.get(),
                0.01
            )
        );
        println!(
            "\x1B[2K    Learning| LBD:{}, trnd:{}, #RST:{}, /dpc:{}",
            fm!("{:>9.2}", self, LogF64Id::EmaLBD, rst_lbd.get_fast(), 0.01),
            fm!("{:>9.2}", self, LogF64Id::TrendLBD, rst_lbd.trend(), 0.01),
            im!("{:>9}", self, LogUsizeId::Restart, rst_num_rst),
            fm!(
                "{:>9.2}",
                self,
                LogF64Id::DecisionPerConflict,
                asg_dpc_ema.get(),
                0.01
            ),
        );
        println!(
            "\x1B[2K        misc|vivC:{}, btdf:{}, core:{}, /ppc:{}",
            im!(
                "{:>9}",
                self,
                LogUsizeId::VivifiedClause,
                self[Stat::VivifiedClause]
            ),
            fm!(
                "{:>9.4}",
                self,
                LogF64Id::BacktrackDriftRate,
                // LogF64Id::ExExTrend,
                // self.e_mode.trend(),
                // self.exploration_rate_ema.get() // , self.e_mode_threshold
                // 100.0 * self.num_chrono_bt as f64 / self[LogUsizeId::NumConflict] as f64
                self.bt_drift_average.get(),
                0.0001
            ),
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
                LogF64Id::PropagationPerConflict,
                asg_ppc_ema.get(),
                0.01
            ),
        );
        self[LogUsizeId::Stage] = self.stm.current_stage();
        self[LogUsizeId::StageCycle] = self.stm.current_cycle();
        self[LogUsizeId::Vivify] = self[Stat::Vivification];
        if self.config.show_cdb_heatmap {
            let big_change = 0.002;
            let heatmap = cdb.clause_heatmap();
            for (i, l) in heatmap.iter().enumerate() {
                let row_label = match i {
                    0 => LogF64Id::CdbHeatmap0,
                    1 => LogF64Id::CdbHeatmap1,
                    2 => LogF64Id::CdbHeatmap2,
                    3 => LogF64Id::CdbHeatmap3,
                    4 => LogF64Id::CdbHeatmap4,
                    5 => LogF64Id::CdbHeatmap5,
                    6 => LogF64Id::CdbHeatmap6,
                    _ => LogF64Id::End,
                };
                let col_labels: [LogF64Id; 8] = match i {
                    0 => [
                        LogF64Id::CdbHeatmapR0C1,
                        LogF64Id::CdbHeatmapR0C2,
                        LogF64Id::CdbHeatmapR0C3,
                        LogF64Id::CdbHeatmapR0C4,
                        LogF64Id::CdbHeatmapR0C5,
                        LogF64Id::CdbHeatmapR0C6,
                        LogF64Id::CdbHeatmapR0C7,
                        LogF64Id::CdbHeatmapR0C8,
                    ],
                    1 => [
                        LogF64Id::CdbHeatmapR1C1,
                        LogF64Id::CdbHeatmapR1C2,
                        LogF64Id::CdbHeatmapR1C3,
                        LogF64Id::CdbHeatmapR1C4,
                        LogF64Id::CdbHeatmapR1C5,
                        LogF64Id::CdbHeatmapR1C6,
                        LogF64Id::CdbHeatmapR1C7,
                        LogF64Id::CdbHeatmapR1C8,
                    ],
                    2 => [
                        LogF64Id::CdbHeatmapR2C1,
                        LogF64Id::CdbHeatmapR2C2,
                        LogF64Id::CdbHeatmapR2C3,
                        LogF64Id::CdbHeatmapR2C4,
                        LogF64Id::CdbHeatmapR2C5,
                        LogF64Id::CdbHeatmapR2C6,
                        LogF64Id::CdbHeatmapR2C7,
                        LogF64Id::CdbHeatmapR2C8,
                    ],
                    3 => [
                        LogF64Id::CdbHeatmapR3C1,
                        LogF64Id::CdbHeatmapR3C2,
                        LogF64Id::CdbHeatmapR3C3,
                        LogF64Id::CdbHeatmapR3C4,
                        LogF64Id::CdbHeatmapR3C5,
                        LogF64Id::CdbHeatmapR3C6,
                        LogF64Id::CdbHeatmapR3C7,
                        LogF64Id::CdbHeatmapR3C8,
                    ],
                    4 => [
                        LogF64Id::CdbHeatmapR4C1,
                        LogF64Id::CdbHeatmapR4C2,
                        LogF64Id::CdbHeatmapR4C3,
                        LogF64Id::CdbHeatmapR4C4,
                        LogF64Id::CdbHeatmapR4C5,
                        LogF64Id::CdbHeatmapR4C6,
                        LogF64Id::CdbHeatmapR4C7,
                        LogF64Id::CdbHeatmapR4C8,
                    ],
                    5 => [
                        LogF64Id::CdbHeatmapR5C1,
                        LogF64Id::CdbHeatmapR5C2,
                        LogF64Id::CdbHeatmapR5C3,
                        LogF64Id::CdbHeatmapR5C4,
                        LogF64Id::CdbHeatmapR5C5,
                        LogF64Id::CdbHeatmapR5C6,
                        LogF64Id::CdbHeatmapR5C7,
                        LogF64Id::CdbHeatmapR5C8,
                    ],
                    _ => [
                        LogF64Id::CdbHeatmapR6C1,
                        LogF64Id::CdbHeatmapR6C2,
                        LogF64Id::CdbHeatmapR6C3,
                        LogF64Id::CdbHeatmapR6C4,
                        LogF64Id::CdbHeatmapR6C5,
                        LogF64Id::CdbHeatmapR6C6,
                        LogF64Id::CdbHeatmapR6C7,
                        LogF64Id::CdbHeatmapR6C8,
                    ],
                };
                let columns = l
                    .iter()
                    .skip(1)
                    .enumerate()
                    .map(|(j, &v)| fm!("{:.3}", self, col_labels[j], v, big_change))
                    .collect::<Vec<_>>()
                    .join(", ");
                if i == heatmap.len() - 1 {
                    println!(
                        "    LBD>{} ({}): {}",
                        i,
                        fm!("{:>5.3}", self, row_label, l[0], big_change),
                        columns
                    );
                } else {
                    println!(
                        "    LBD {} ({}): {}",
                        i + 1,
                        fm!("{:>5.3}", self, row_label, l[0], big_change),
                        columns
                    );
                }
            }
        }
        self.flush("");
    }
}

impl State {
    #[allow(clippy::cognitive_complexity)]
    fn record_stats<A, C>(&mut self, asg: &A, cdb: &C)
    where
        A: PropertyDereference<assign::property::Tusize, usize>
            + PropertyReference<assign::property::TEma, EmaView>,
        C: PropertyDereference<cdb::property::Tusize, usize>
            + PropertyDereference<cdb::property::Tf64, f64>
            + PropertyReference<cdb::property::TEma, EmaView>,
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
        self[LogUsizeId::Restart] = self[Stat::Restart];
        self[LogUsizeId::Stage] = self.stm.current_stage();
        self[LogUsizeId::StageCycle] = self.stm.current_cycle();
        self[LogUsizeId::StageSegment] = self.stm.max_scale();
        self[LogUsizeId::Simplify] = self[Stat::Simplify];
        self[LogUsizeId::SubsumedClause] = self[Stat::SubsumedClause];
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
            CNFIndicator::LitVec(n) => format!("(embedded {n} element vector)"),
        };
        if width <= fname.len() {
            fname.truncate(58 - vclen);
        }
        let fnlen = fname.len();
        if width < vclen + fnlen + 1 {
            write!(f, "{fname:<width$} |time:{tm:>9.2}")
        } else {
            write!(f, "{fname}{:>w$} |time:{tm:>9.2}", &vc, w = width - fnlen,)
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
    //## restart
    //
    Restart,

    //
    //## stage
    //
    Stage,
    StageCycle,
    StageSegment,

    //
    //## pre(in)-processor
    //
    Simplify,
    SubsumedClause,
    VivifiedClause,
    VivifiedVar,
    Vivify,

    //
    //## Stochastic Local Search
    //
    SLS,

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
    BacktrackDriftRate,
    ExExTrend,
    DecisionPerConflict,
    ConflictPerRestart,
    PropagationPerConflict,
    LiteralBlockEntanglement,
    RestartEnergy,
    ChronologicalBacktrackPercentage,
    CdbHeatmap0,
    CdbHeatmap1,
    CdbHeatmap2,
    CdbHeatmap3,
    CdbHeatmap4,
    CdbHeatmap5,
    CdbHeatmap6,
    CdbHeatmapR0C1,
    CdbHeatmapR0C2,
    CdbHeatmapR0C3,
    CdbHeatmapR0C4,
    CdbHeatmapR0C5,
    CdbHeatmapR0C6,
    CdbHeatmapR0C7,
    CdbHeatmapR0C8,
    CdbHeatmapR1C1,
    CdbHeatmapR1C2,
    CdbHeatmapR1C3,
    CdbHeatmapR1C4,
    CdbHeatmapR1C5,
    CdbHeatmapR1C6,
    CdbHeatmapR1C7,
    CdbHeatmapR1C8,
    CdbHeatmapR2C1,
    CdbHeatmapR2C2,
    CdbHeatmapR2C3,
    CdbHeatmapR2C4,
    CdbHeatmapR2C5,
    CdbHeatmapR2C6,
    CdbHeatmapR2C7,
    CdbHeatmapR2C8,
    CdbHeatmapR3C1,
    CdbHeatmapR3C2,
    CdbHeatmapR3C3,
    CdbHeatmapR3C4,
    CdbHeatmapR3C5,
    CdbHeatmapR3C6,
    CdbHeatmapR3C7,
    CdbHeatmapR3C8,
    CdbHeatmapR4C1,
    CdbHeatmapR4C2,
    CdbHeatmapR4C3,
    CdbHeatmapR4C4,
    CdbHeatmapR4C5,
    CdbHeatmapR4C6,
    CdbHeatmapR4C7,
    CdbHeatmapR4C8,
    CdbHeatmapR5C1,
    CdbHeatmapR5C2,
    CdbHeatmapR5C3,
    CdbHeatmapR5C4,
    CdbHeatmapR5C5,
    CdbHeatmapR5C6,
    CdbHeatmapR5C7,
    CdbHeatmapR5C8,
    CdbHeatmapR6C1,
    CdbHeatmapR6C2,
    CdbHeatmapR6C3,
    CdbHeatmapR6C4,
    CdbHeatmapR6C5,
    CdbHeatmapR6C6,
    CdbHeatmapR6C7,
    CdbHeatmapR6C8,

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

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Tusize {
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

    pub const USIZES: [Tusize; 7] = [
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

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum Tf64 {
        /// the number of chronoBT / the number of BT
        ChronologicalBacktrackRate,
    }

    pub const F64S: [Tf64; 1] = [Tf64::ChronologicalBacktrackRate];

    impl PropertyDereference<Tf64, f64> for State {
        #[inline]
        fn derefer(&self, k: Tf64) -> f64 {
            match k {
                Tf64::ChronologicalBacktrackRate => {
                    self.num_chrono_bt as f64 / self[LogUsizeId::NumConflict] as f64
                }
            }
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub enum TEma {
        BackjumpLevel,
        ConflictLevel,
    }

    pub const EMAS: [TEma; 2] = [TEma::BackjumpLevel, TEma::ConflictLevel];

    impl PropertyReference<TEma, EmaView> for State {
        #[inline]
        fn refer(&self, k: TEma) -> &EmaView {
            match k {
                TEma::BackjumpLevel => self.b_lvl.as_view(),
                TEma::ConflictLevel => self.c_lvl.as_view(),
            }
        }
    }
}

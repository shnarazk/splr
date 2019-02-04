use crate::clause::ClauseDB;
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::restart::Ema;
use crate::traits::*;
use crate::types::*;
use crate::var::Var;
use std::fmt;
use std::path::Path;
use std::time::SystemTime;

/// stat index
#[derive(Clone, Eq, PartialEq)]
pub enum Stat {
    Conflict = 0,       // the number of backjump
    Decision,           // the number of decision
    Restart,            // the number of restart
    RestartRecord,      // the last recorded number of Restart
    BlockRestart,       // the number of blacking start
    BlockRestartRecord, // the last recorded number of BlockResatr
    Learnt,             // the number of learnt clauses (< Conflict)
    NoDecisionConflict, // the number of 'no decision conflict'
    Propagation,        // the number of propagation
    Reduction,          // the number of reduction
    Simplification,     // the number of simplification
    Elimination,        // the number of clause subsumption and varibale elimination
    Assign,             // the number of assigned variables
    SumLBD,             // the sum of generated learnts' LBD
    NumBin,             // the number of binary clauses
    NumBinLearnt,       // the number of binary learnt clauses
    NumLBD2,            // the number of clauses which LBD is 2
    EndOfStatIndex,     // Don't use this dummy.
}

pub struct State {
    pub ok: bool,
    pub next_reduction: usize, // renamed from `nbclausesbeforereduce`
    pub next_restart: usize,
    pub cur_restart: usize,
    pub after_restart: usize,
    pub elim_trigger: usize,
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
    pub an_seen: Vec<bool>,
    pub lbd_temp: Vec<usize>,
    pub start: SystemTime,
    dumper: ProgressRecord,
    pub progress_cnt: usize,
    pub target: CNFDescription,
}

macro_rules! i {
    ($format: expr, $dumper: expr, $key: expr, $val: expr) => {
        match $val {
            v => {
                let ptr = &mut $dumper.vali[$key as usize];
                if v < *ptr {
                    *ptr = v;
                    format!("\x1B[031m{}\x1B[000m", format!($format, *ptr))
                } else if *ptr < v {
                    *ptr = v;
                    format!("\x1B[001m{}\x1B[000m", format!($format, *ptr))
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
                if v < *ptr {
                    *ptr = v;
                    format!("\x1B[031m{}\x1B[000m", format!($format, *ptr))
                } else if *ptr < v {
                    *ptr = v;
                    format!("\x1B[001m{}\x1B[000m", format!($format, *ptr))
                } else {
                    *ptr = v;
                    format!($format, *ptr)
                }
            }
        }
    };
}

impl StateIF for State {
    fn new(config: &Config, mut cnf: CNFDescription) -> State {
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
        State {
            ok: true,
            next_reduction: 1000,
            next_restart: 100,
            cur_restart: 1,
            after_restart: 0,
            elim_trigger: 1,
            stats: [0; Stat::EndOfStatIndex as usize],
            ema_asg: Ema::new(config.restart_asg_len),
            ema_lbd: Ema::new(config.restart_lbd_len),
            b_lvl: Ema::new(5_000),
            c_lvl: Ema::new(5_000),
            sum_asg: 0.0,
            num_solved_vars: 0,
            num_eliminated_vars: 0,
            model: vec![BOTTOM; cnf.num_of_variables + 1],
            conflicts: vec![],
            an_seen: vec![false; cnf.num_of_variables + 1],
            lbd_temp: vec![0; cnf.num_of_variables + 1],
            start: SystemTime::now(),
            progress_cnt: 0,
            dumper: ProgressRecord::default(),
            target: cnf,
        }
    }
    fn progress_header(&self, config: &Config) {
        if config.progress_log {
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
    }
    #[allow(clippy::cyclomatic_complexity)]
    fn progress(
        &mut self,
        cdb: &ClauseDB,
        config: &mut Config,
        elim: &Eliminator,
        vars: &[Var],
        mes: Option<&str>,
    ) {
        if config.progress_log {
            self.dump(cdb, config, elim, vars, mes);
            return;
        }
        let nv = vars.len() - 1;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        self.progress_cnt += 1;
        print!("\x1B[7A");
        let msg = match mes {
            None => config.strategy.to_str(),
            Some(x) => x,
        };
        let count = self.stats[Stat::Conflict as usize];
        let ave = self.stats[Stat::SumLBD as usize] as f64 / count as f64;
        println!("{}, Mode:{:>9}", self, msg);
        println!(
            " #conflict:{}, #decision:{}, #propagate:{} ",
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
            "  Assignment|#rem:{}, #fix:{}, #elm:{}, prg%:{} ",
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
            " Clause Kind|Remv:{}, LBD2:{}, Binc:{}, Perm:{} ",
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
            "     Restart|#BLK:{}, #RST:{}, eASG:{}, eLBD:{} ",
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
            "   Conflicts|aLBD:{}, bjmp:{}, cnfl:{} |blkR:{} ",
            f!("{:>9.2}", self.dumper, LogF64Id::AveLBD, self.ema_lbd.get()),
            f!("{:>9.2}", self.dumper, LogF64Id::BLevel, self.b_lvl.get()),
            f!("{:>9.2}", self.dumper, LogF64Id::CLevel, self.c_lvl.get()),
            f!(
                "{:>9.4}",
                self.dumper,
                LogF64Id::RestartBlkR,
                config.restart_blk
            ),
        );
        println!(
            "   Clause DB|#rdc:{}, #smp:{}, #elm:{} |rstK:{} ",
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::Reduction,
                self.stats[Stat::Reduction as usize]
            ),
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::Simplification,
                self.stats[Stat::Simplification as usize]
            ),
            i!(
                "{:>9}",
                self.dumper,
                LogUsizeId::Elimination,
                self.stats[Stat::Elimination as usize]
            ),
            f!(
                "{:>9.4}",
                self.dumper,
                LogF64Id::RestartThrK,
                config.restart_thr
            ),
        );
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
        let width = 43;
        if width < vclen + fnlen {
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

enum LogUsizeId {
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
    Simplification, // 13: simplification: usize,
    Elimination,    // 14: elimination: usize,
    // ElimClauseQueue, // 15: elim_clause_queue: usize,
    // ElimVarQueue, // 16: elim_var_queue: usize,
    End,
}

enum LogF64Id {
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

struct ProgressRecord {
    vali: [usize; LogUsizeId::End as usize],
    valf: [f64; LogF64Id::End as usize],
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
    fn dump(
        &mut self,
        cdb: &ClauseDB,
        _config: &mut Config,
        _elim: &Eliminator,
        vars: &[Var],
        _mes: Option<&str>,
    ) {
        self.progress_cnt += 1;
        let nv = vars.len() - 1;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        let nlearnts = cdb.countf(1 << Flag::DeadClause as u16 | 1 << Flag::LearntClause as u16);
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
    fn dump_details(
        &mut self,
        cdb: &ClauseDB,
        config: &mut Config,
        elim: &Eliminator,
        vars: &[Var],
        mes: Option<&str>,
    ) {
        self.progress_cnt += 1;
        let msg = match mes {
            None => config.strategy.to_str(),
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

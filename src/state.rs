use crate::clause::ClauseDB;
use crate::config::Config;
use crate::eliminator::Eliminator;
use crate::restart::Ema;
use crate::traits::*;
use crate::types::*;
use crate::var::Var;
use chrono::Utc;
use std::fmt;
use std::path::Path;

/// stat index
#[derive(Clone, Eq, PartialEq)]
pub enum Stat {
    Conflict = 0,       // the number of backjump
    Decision,           // the number of decision
    Restart,            // the number of restart
    Learnt,             // the number of learnt clauses (< Conflict)
    NoDecisionConflict, // the number of 'no decision conflict'
    BlockRestart,       // the number of blacking start
    Propagation,        // the number of propagation
    Reduction,          // the number of reduction
    Simplification,     // the number of simplification
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
    pub start: chrono::DateTime<chrono::Utc>,
    pub progress_cnt: usize,
    pub target: String,
}

impl StateIF for State {
    fn new(config: &Config, nv: usize, _se: i32, fname: &str) -> State {
        State {
            ok: true,
            next_reduction: 1000,
            next_restart: 100,
            cur_restart: 1,
            after_restart: 0,
            stats: [0; Stat::EndOfStatIndex as usize],
            ema_asg: Ema::new(config.restart_asg_len),
            ema_lbd: Ema::new(config.restart_lbd_len),
            b_lvl: Ema::new(5_000),
            c_lvl: Ema::new(5_000),
            sum_asg: 0.0,
            num_solved_vars: 0,
            num_eliminated_vars: 0,
            model: vec![BOTTOM; nv + 1],
            conflicts: vec![],
            an_seen: vec![false; nv + 1],
            lbd_temp: vec![0; nv + 1],
            start: Utc::now(),
            progress_cnt: 0,
            target: if fname == "" {
                "--".to_string()
            } else {
                Path::new(&fname)
                    .file_name()
                    .unwrap()
                    .to_os_string()
                    .into_string()
                    .unwrap()
            },
        }
    }

    fn progress(
        &mut self,
        cdb: &ClauseDB,
        config: &mut Config,
        elim: &Eliminator,
        vars: &[Var],
        mes: Option<&str>,
    ) {
        if mes != Some("") {
            self.progress_cnt += 1;
        }
        let nv = vars.len() - 1;
        let fixed = self.num_solved_vars;
        let sum = fixed + self.num_eliminated_vars;
        if !config.progress_log {
            if mes == Some("") {
                println!("{}", self);
                println!();
                println!();
                println!();
                println!();
                println!();
                println!();
            } else {
                print!("\x1B[7A");
                let msg = match mes {
                    None => config.strategy.to_str(),
                    Some(x) => x,
                };
                let count = self.stats[Stat::Conflict as usize];
                let ave = self.stats[Stat::SumLBD as usize] as f64 / count as f64;
                println!("{}, Str:{:>8}", self, msg);
                println!(
                    "#propagate:{:>14}, #decision:{:>13}, #conflict: {:>12} ",
                    self.stats[Stat::Propagation as usize],
                    self.stats[Stat::Decision as usize],
                    self.stats[Stat::Conflict as usize],
                );
                println!(
                    "  Assignment|#rem:{:>9}, #fix:{:>9}, #elm:{:>9}, prg%:{:>9.4} ",
                    nv - sum,
                    fixed,
                    self.num_eliminated_vars,
                    (sum as f32) / (nv as f32) * 100.0,
                );
                println!(
                    " Clause Kind|Remv:{:>9}, LBD2:{:>9}, Binc:{:>9}, Perm:{:>9} ",
                    cdb.num_learnt,
                    self.stats[Stat::NumLBD2 as usize],
                    self.stats[Stat::NumBinLearnt as usize],
                    cdb.num_active - cdb.num_learnt,
                );
                println!(
                    "     Restart|#BLK:{:>9}, #RST:{:>9}, eASG:{:>9.4}, eLBD:{:>9.4} ",
                    self.stats[Stat::BlockRestart as usize],
                    self.stats[Stat::Restart as usize],
                    self.ema_asg.get() / nv as f64,
                    self.ema_lbd.get() / ave,
                );
                println!(
                    "   Conflicts|aLBD:{:>9.2}, bjmp:{:>9.2}, cnfl:{:>9.2} |#cls:{:>9} ",
                    self.ema_lbd.get(),
                    self.b_lvl.get(),
                    self.c_lvl.get(),
                    elim.clause_queue_len(),
                );
                println!(
                    "   Clause DB|#rdc:{:>9}, #smp:{:>9},      Eliminator|#var:{:>9} ",
                    self.stats[Stat::Reduction as usize],
                    self.stats[Stat::Simplification as usize],
                    elim.var_queue_len(),
                );
            }
        } else if mes == Some("") {
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
        } else {
            let msg = match mes {
                None => config.strategy.to_str(),
                Some(x) => x,
            };
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
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut tm = format!("{}", Utc::now() - self.start);
        tm.drain(..2);
        tm.pop();
        write!(f, "{:36}|time:{:>19}", self.target, tm)
    }
}

enum LogUsizeId {
    Propagate = 0,   //  0: propagate: usize,
    Decision,        //  1: decision: usize,
    Conflict,        //  2: conflict: usize,
    Remain,          //  3: remain: usize,
    Fixed,           //  4: fixed: usize,
    Eliminated,      //  5: elim: usize,
    Removable,       //  6: removable: usize,
    LBD2,            //  7: lbd2: usize,
    Binclause,       //  8: binclause: usize,
    Permanent,       //  9: permanent: usize,
    RestartBlock,    // 10: restart_block: usize,
    Restart,         // 11: restart_count: usize,
    Reduction,       // 12: reduction: usize,
    Simplification,  // 13: simplification: usize,
    ElimClauseQueue, // 14: elim_clause_queue: usize,
    ElimVarQueue,    // 15: elim_var_queue: usize,
}

enum LogF64Id {
    Progress = 0, //  0: progress: f64,
    EmaAsg,       //  1: ema_asg: f64,
    EmaLBD,       //  2: ema_lbd: f64,
    AveLBD,       //  3: ave_lbd: f64,
    BLevel,       //  4: backjump_level: f64,
    CLevel,       //  5: conflict_level: f64,
}

struct ProgressRecord {
    vali: [usize; 16],
    valf: [f64; 6],
    //  0: propagate: usize,
    //  1: decision: usize,
    //  2: conflict: usize,
    //  3: remain: usize,
    //  4: fixed: usize,
    //  5: elim: usize,
    //  0: progress: f64,
    //  6: removable: usize,
    //  7: lbd2: usize,
    //  8: binclause: usize,
    //  9: permanent: usize,
    // 10: restart_block: usize,
    // 11: restart_count: usize,
    //  1: ema_asg: f64,
    //  2: ema_lbd: f64,
    //  3: ave_lbd: f64,
    //  4: backjump_level: f64,
    //  5: conflict_level: f64,
    // 12: reduction: usize,
    // 13: simplification: usize,
    // 14: elim_clause_queue: usize,
    // 15: elim_var_queue: usize,
}

impl ProgressRecord {
    i2s(&mut self, f: LogUsizeId, x: usize) -> str {
        if x < self.vali[f] {
            self.vali[f] = x;
            format!("xxxx{:>9}", self.f)
        } else {
            self.vali[f] = x;
            format!("{:>9}", self.f)
        }
    }
    f2s(&mut self, f: LogF64Id, x: f64) -> str {
        if x < self.valf[f] {
            self.valf[f] = x;
            format!("xxxx{:>9.4}", x)
        } else {
            self.valf[f] = x;
            format!("{:>9.4}", x)
        }
    }
}

trait Log {
    fn pro_header(&self) -> str;
    fn pro(
        &mut self,
        cdb: &ClauseDB,
        config: &mut Config,
        elim: &Eliminator,
        vars: &[Var],
        mes: Option<&str>,
    ) -> str;
}

impl Log for ProgressRecord { 
    fn pro_header(&self) {
        println!("{:?}", self);
        println!();
        println!();
        println!();
        println!();
        println!();
        println!();
    }
    fn pro(
        &mut self,
        cdb: &ClauseDB,
        config: &mut Config,
        elim: &Eliminator,
        vars: &[Var],
        mes: Option<&str>,
    ) {
        self.progress_cnt += 1;
        print!("\x1B[7A");
        let msg = match mes {
            None => config.strategy.to_str(),
            Some(x) => x,
        };
        let count = self.stats[Stat::Conflict as usize];
        let ave = self.stats[Stat::SumLBD as usize] as f64 / count as f64;
        println!("{}, Str:{:>8}", self, msg);
        println!(
            "#propagate:{:>14}, #decision:{:>13}, #conflict: {:>12} ",
            self.stats[Stat::Propagation as usize],
            self.stats[Stat::Decision as usize],
            self.stats[Stat::Conflict as usize],
        );
        println!(
            "  Assignment|#rem:{:>9}, #fix:{:>9}, #elm:{:>9}, prg%:{:>9.4} ",
            nv - sum,
            fixed,
            self.num_eliminated_vars,
            (sum as f32) / (nv as f32) * 100.0,
        );
        println!(
            " Clause Kind|Remv:{:>9}, LBD2:{:>9}, Binc:{:>9}, Perm:{:>9} ",
            cdb.num_learnt,
            self.stats[Stat::NumLBD2 as usize],
            self.stats[Stat::NumBinLearnt as usize],
            cdb.num_active - cdb.num_learnt,
        );
        println!(
            "     Restart|#BLK:{:>9}, #RST:{:>9}, eASG:{:>9.4}, eLBD:{:>9.4} ",
            self.stats[Stat::BlockRestart as usize],
            self.stats[Stat::Restart as usize],
            self.ema_asg.get() / nv as f64,
            self.ema_lbd.get() / ave,
        );
        println!(
            "   Conflicts|aLBD:{:>9.2}, bjmp:{:>9.2}, cnfl:{:>9.2} |#cls:{:>9} ",
            self.ema_lbd.get(),
            self.b_lvl.get(),
            self.c_lvl.get(),
            elim.clause_queue_len(),
        );
        println!(
            "   Clause DB|#rdc:{:>9}, #smp:{:>9},      Eliminator|#var:{:>9} ",
            self.stats[Stat::Reduction as usize],
            self.stats[Stat::Simplification as usize],
            elim.var_queue_len(),
        );
    }
}

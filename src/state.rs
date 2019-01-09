use crate::assign::AssignStack;
use crate::clause::{ClauseDB, ClauseKind};
use crate::config::SolverConfig;
use crate::eliminator::Eliminator;
use crate::traits::*;
use crate::types::*;
use crate::var::{Var, VarIdHeap};
use chrono::Utc;
use std::collections::VecDeque;
use std::fmt;
use std::path::Path;

/// stat index
#[derive(Clone, Eq, PartialEq)]
pub enum Stat {
    Conflict = 0,       // the number of backjump
    Decision,           // the number of decision
    Restart,            // the number of restart
    NoDecisionConflict, // the number of 'no decision conflict'
    BlockRestart,       // the number of blacking start
    Propagation,        // the number of propagation
    Reduction,          // the number of reduction
    Simplification,     // the number of simplification
    Assign,             // the number of assigned variables
    SumLBD,             // the sum of generated learnts' LBD
    NumBin,             // the number of binary clauses
    NumLBD2,            // the number of clauses which LBD is 2
    EndOfStatIndex,     // Don't use this dummy.
}

pub struct SolverState {
    pub ok: bool,
    pub next_reduction: usize, // renamed from `nbclausesbeforereduce`
    pub next_restart: usize,
    pub cur_restart: usize,
    pub after_restart: usize,
    pub lbd_queue: VecDeque<usize>,
    pub trail_queue: VecDeque<usize>,
    pub var_order: VarIdHeap, // Variable Order
    pub stats: Vec<i64>,      // statistics
    pub ema_asg: Ema2,
    pub ema_lbd: Ema2,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub num_solved_vars: usize,
    pub model: Vec<Lbool>,
    pub conflicts: Vec<Lit>,
    pub an_seen: Vec<bool>,
    pub lbd_temp: Vec<usize>,
    pub start: chrono::DateTime<chrono::Utc>,
    pub progress_cnt: usize,
    pub target: String,
}

impl SolverStateIF for SolverState {
    fn new(nv: usize, _se: i32, fname: &str) -> SolverState {
        SolverState {
            ok: true,
            next_reduction: 1000,
            next_restart: 100,
            cur_restart: 1,
            after_restart: 0,
            lbd_queue: VecDeque::new(),
            trail_queue: VecDeque::new(),
            var_order: VarIdHeap::new(nv, nv),
            stats: vec![0; Stat::EndOfStatIndex as usize],
            ema_asg: Ema2::new(80.0, 50_000.0),
            ema_lbd: Ema2::new(50.0, 50_000.0),
            b_lvl: Ema::new(50_000),
            c_lvl: Ema::new(50_000),
            num_solved_vars: 0,
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
        asgs: &AssignStack,
        config: &mut SolverConfig,
        cp: &ClauseDB,
        elim: &Eliminator,
        vars: &[Var],
        mes: Option<&str>,
    ) {
        if mes != Some("") {
            self.progress_cnt += 1;
        }
        // if self.progress_cnt % 16 == 0 {
        //     self.dump_cnf(format!("G2-p{:>3}.cnf", self.progress_cnt).to_string());
        // }
        let nv = vars.len() - 1;
        let fixed = if asgs.is_zero() {
            asgs.len()
        } else {
            asgs.num_at(0)
        };
        let sum = fixed + elim.eliminated_vars;
        let good = -1;
        //let learnts = &cp[ClauseKind::Removable as usize];
        // let good = learnts
        //     .head
        //     .iter()
        //     .skip(1)
        //     .filter(|c| !c.get_flag(ClauseFlag::Dead) && c.rank <= 3)
        //     .count();
        if config.use_tty {
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
                println!("{}, State:{:>6}", self, msg,);
                println!(
                    "#propagate:{:>14}, #decision:{:>13}, #conflict: {:>12} ",
                    self.stats[Stat::Propagation as usize],
                    self.stats[Stat::Decision as usize],
                    self.stats[Stat::Conflict as usize],
                );
                println!(
                    "  Assignment|#rem:{:>9}, #fix:{:>9}, #elm:{:>9}, prog%:{:>8.4} ",
                    nv - sum,
                    fixed,
                    elim.eliminated_vars,
                    (sum as f32) / (nv as f32) * 100.0,
                );
                println!(
                    "   Clause DB|Remv:{:>9}, good:{:>9}, Perm:{:>9}, Binc:{:>9} ",
                    cp[ClauseKind::Removable as usize].count(true),
                    good,
                    cp[ClauseKind::Permanent as usize].count(true),
                    cp[ClauseKind::Binclause as usize].count(true),
                );
                println!(
                    "     Restart|#BLK:{:>9}, #RST:{:>9}, emaASG:{:>7.2}, emaLBD:{:>7.2} ",
                    self.stats[Stat::BlockRestart as usize],
                    self.stats[Stat::Restart as usize],
                    self.ema_asg.get(),
                    self.ema_lbd.get(),
                );
                println!(
                    " Decision Lv|aLBD:{:>9.2}, bjmp:{:>9.2}, cnfl:{:>9.2} |#rdc:{:>9} ",
                    self.ema_lbd.slow,
                    self.b_lvl.0,
                    self.c_lvl.0,
                    self.stats[Stat::Reduction as usize],
                );
                println!(
                    "  Eliminator|#cls:{:>9}, #var:{:>9},   Clause DB mgr|#smp:{:>9} ",
                    elim.clause_queue_len(),
                    elim.var_queue_len(),
                    self.stats[Stat::Simplification as usize],
                );
            }
        } else if mes == Some("") {
            println!(
                "   #mode,      Variable Assignment      ,,  \
                 Clause Database Management  ,,   Restart Strategy      ,, \
                 Misc Progress Parameters,,  Eliminator"
            );
            println!(
                "   #init,#remain,#solved,   #elim,total%,,#learnt,(good),  \
                 #perm,#binary,,block,force, asgn/,  lbd/,,    lbd, \
                 back lv, conf lv,,clause,   var"
            );
        } else {
            let msg = match mes {
                None => config.strategy.to_str(),
                Some(x) => x,
            };
            println!(
                "{:>3}#{:<5},{:>7},{:>7},{:>7},{:>6.3},,{:>7},{:>6},{:>7},\
                 {:>7},,{:>5},{:>5}, {:>5.2},{:>6.2},,{:>7.2},{:>8.2},{:>8.2},,\
                 {:>6},{:>6}",
                self.progress_cnt,
                msg,
                nv - sum,
                fixed,
                elim.eliminated_vars,
                (sum as f32) / (nv as f32) * 100.0,
                cp[ClauseKind::Removable as usize].count(true),
                good,
                cp[ClauseKind::Permanent as usize].count(true),
                cp[ClauseKind::Binclause as usize].count(true),
                self.stats[Stat::BlockRestart as usize],
                self.stats[Stat::Restart as usize],
                self.ema_asg.get(),
                self.ema_lbd.get(),
                self.ema_lbd.slow,
                self.b_lvl.0,
                self.c_lvl.0,
                elim.clause_queue_len(),
                elim.var_queue_len(),
            );
        }
    }

    #[allow(dead_code)]
    fn dump(&self, asgs: &AssignStack, str: &str) {
        println!("# {} at {}", str, asgs.level());
        println!(
            "# nassigns {}, decision cands {}",
            asgs.len(),
            self.var_order.len()
        );
        let v = asgs.trail.iter().map(|l| l.int()).collect::<Vec<i32>>();
        let len = asgs.level();
        if 0 < len {
            print!("# - trail[{}]  [", asgs.len());
            let lv0 = asgs.num_at(0);
            if 0 < lv0 {
                print!("0{:?}, ", &asgs.trail[0..lv0]);
            }
            for i in 0..(len - 1) {
                let a = asgs.num_at(i);
                let b = asgs.num_at(i + 1);
                print!("{}{:?}, ", i + 1, &v[a..b]);
            }
            println!("{}{:?}]", len, &v[asgs.num_at(len - 1)..]);
        } else {
            println!("# - trail[  0]  [0{:?}]", &v);
        }
        println!("- trail_lim  {:?}", asgs.trail_lim);
        // println!("{}", self.var_order);
        // self.var_order.check("");
    }
}

impl fmt::Display for SolverState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut tm = format!("{}", Utc::now() - self.start);
        tm.drain(..2);
        tm.pop();
        write!(f, "{:36}|time:{:>19}", self.target, tm)
    }
}

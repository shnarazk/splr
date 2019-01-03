use crate::types::*;
use crate::var::VarIdHeap;
use chrono::*;
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

pub struct Profile {
    pub var_order: VarIdHeap, // Variable Order
    pub stat: Vec<i64>,       // statistics
    pub ema_asg: Ema2,
    pub ema_lbd: Ema2,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub start: chrono::DateTime<chrono::Utc>,
    pub progress_cnt: usize,
    pub target: String,
}

impl Profile {
    pub fn new(nv: usize, se: i32, fname: &str) -> Profile {
        Profile {
            var_order: VarIdHeap::new(nv, nv),
            stat: vec![0; Stat::EndOfStatIndex as usize],
            ema_asg: Ema2::new(3.8, 50_000.0),   // for blocking 4
            ema_lbd: Ema2::new(160.0, 50_000.0), // for forcing 160
            b_lvl: Ema::new(se),
            c_lvl: Ema::new(se),
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
}

impl fmt::Display for Profile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut tm = format!("{}", Utc::now() - self.start);
        tm.drain(..2);
        tm.pop();
        write!(f, "{:36}|time:{:>19}", self.target, tm)
    }
}

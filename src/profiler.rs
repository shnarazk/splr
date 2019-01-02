use crate::types::*;
use chrono::*;
use std::fmt;
use std::path::Path;

pub struct Profile {
    pub progress_cnt: usize,
    pub start: chrono::DateTime<chrono::Utc>,
    pub ema_asg: Ema2,
    pub ema_lbd: Ema2,
    pub b_lvl: Ema,
    pub c_lvl: Ema,
    pub target: String,
}

impl Profile {
    pub fn new(se: i32, fname: &str) -> Profile {
        Profile {
            progress_cnt: 0,
            start: Utc::now(),
            ema_asg: Ema2::new(3.8, 50_000.0),   // for blocking 4
            ema_lbd: Ema2::new(160.0, 50_000.0), // for forcing 160
            b_lvl: Ema::new(se),
            c_lvl: Ema::new(se),
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

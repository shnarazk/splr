extern crate chrono;
use self::chrono::*;
use std::fmt;
use std::path::Path;

pub struct Profile {
    pub start: self::chrono::DateTime<self::chrono::Utc>,
    pub target: String,
}

impl Profile {
    pub fn new(fname: &str) -> Profile {
        Profile {
            start: Utc::now(),
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

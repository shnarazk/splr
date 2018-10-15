extern crate chrono;
use self::chrono::*;
use std::fmt;
use std::path::Path;

#[derive(Debug)]
pub struct Profile {
    pub start: self::chrono::DateTime<self::chrono::Utc>,
    pub target: String,
}

impl Profile {
    pub fn new(fname: String) -> Profile {
        Profile {
            start: Utc::now(),
            target: Path::new(&fname).file_name().unwrap().to_os_string().into_string().unwrap(),
        }
    }
}

impl fmt::Display for Profile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}| {}, {:?}",
            self.target,
            Utc::now() - self.start,
            self.start,
        )
    }
}

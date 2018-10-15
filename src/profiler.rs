extern crate chrono;
use self::chrono::*;
use std::fmt;

#[derive(Debug)]
pub struct Profile {
    pub start: self::chrono::DateTime<self::chrono::Utc>,
    pub target: String,
}

impl Profile {
    pub fn new(target: String) -> Profile {
        Profile {
            start: Utc::now(),
            target, 
        }
    }
}

impl fmt::Display for Profile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}, {} ({})",
            self.target,
            Utc::now() - self.start,
            self.start,
        )
    }
}


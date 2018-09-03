#![allow(unused_imports)]
/// Model checker for Satisfiability in Rust
extern crate splr;
use splr::solver::{SatSolver, Solver};
use std::env;
// use std::fs::File;
use std::io::{BufReader, BufRead, stdin};
use splr::types::*;
use splr::validator::*;
use std::path::Path;

const VERSION: &str = "mcsr-0.0.1";

fn main() {
    let mut target: Option<String> = None;
    let args: Vec<String> = env::args().skip(1).collect();
    for arg in &args {
        match arg {
            _ if arg.to_string() == "--version" => {
                println!("{}", VERSION);
            }
            _ if (&*arg).starts_with('-') => {
                continue;
            }
            _ => {
                target = Some(arg.to_string());
            }
        }
    }
    if let Some(path) = target {
        // let file = Path::new(&path);
        let (mut s, _cnf) = Solver::build(&path);
        // println!("read the problem.");
        s.inject_assigmnent(&read_assignment());
        // println!("read an assignment.");
        if s.validate() {
            println!("Valid assignment for {}.", path);
        } else {
            println!("Invalid assignment for {}.", path);
        }
    }
}

fn read_assignment() -> Vec<i32> {
    let mut rs = BufReader::new(stdin());
    let mut buf = String::new();
    loop {
        match rs.read_line(&mut buf) {
            Ok(0) => return Vec::new(),
            Ok(_) => {
                if buf.starts_with("c") {
                    continue;
                }
                let mut v: Vec<i32> = Vec::new();
                for s in buf.split_whitespace() {
                    match s.parse::<i32>() {
                        Ok(0) => break,
                        Ok(x) => v.push(x),
                        Err(e) => panic!("{} by {}", e, s),
                    }
                }
                return v;
            }
            Err(e) => panic!("{}", e),
        }
    }
}

// DIMACS Model Checker in Rust
#![allow(unused_imports)]
extern crate splr;
use splr::solver::{SatSolver, Solver};
use std::env;
use std::io::{BufReader, BufRead, stdin};
use splr::types::*;
use splr::validator::*;
use std::path::Path;

const VERSION: &str = "dmcr-0.0.1";

fn main() {
    let mut target: Option<String> = None;
    for arg in &env::args().skip(1).collect::<Vec<String>>() {
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
        let (mut s, _cnf) = Solver::build(&path);
        // println!("read the problem.");
        s.inject_assigmnent(&read_assignment());
        // println!("read an assignment.");
        match s.validate() {
            Some(v) => println!("Invalid assignment for {} due to {:?}.", path, v),
            None => println!("Valid assignment for {}.", path),
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

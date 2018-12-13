// DIMACS Model Checker in Rust
#![allow(unused_imports)]
use splr::solver::{SatSolver, Solver};
use splr::types::*;
use splr::validator::*;
use std::env;
use std::io::{stdin, BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::fs;
use structopt::StructOpt;

const VERSION: &str = "dmcr-0.0.2";

#[derive(StructOpt, Debug)]
#[structopt(name = "dmcr", about = "DIMACS-format Model Checker in Rust")]
struct TargetOpts {
    #[structopt(parse(from_os_str))]
    #[structopt(short = "a", long = "assign")]
    answer: Option<std::path::PathBuf>,
    #[structopt(parse(from_os_str))]
    problem: std::path::PathBuf,
}

fn main() {
    let mut found = false;
    let answer;
    let args = TargetOpts::from_args();
    let (mut s, _cnf) = Solver::build(&args.problem.to_str().unwrap());
    if args.answer == None {
        let p = format!(".ans_{}", args.problem.to_str().unwrap());
        found = true;
        answer = PathBuf::from(p);
    } else {
        answer = args.answer.unwrap();
    }
    s.inject_assigmnent(&read_assignment(&answer));
    match s.validate() {
        Some(v) => println!("Invalid assignment for {} due to {:?}.", args.problem.to_str().unwrap(), v),
        None if found => println!("Valid assignment for {} found in {}.",
                                  &args.problem.to_str().unwrap(),
                                  answer.to_str().unwrap(),
        ),
        None  =>  println!("Valid assignment for {}.",
                           &args.problem.to_str().unwrap()),
    }
}

fn read_assignment(path: &Path) -> Vec<i32> {
    let mut rs = BufReader::new(fs::File::open(path).unwrap());
    // let mut rs = BufReader::new(stdin());
    let mut buf = String::new();
    loop {
        match rs.read_line(&mut buf) {
            Ok(0) => return Vec::new(),
            Ok(_) => {
                if buf.starts_with('c') {
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

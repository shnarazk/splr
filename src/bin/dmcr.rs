// DIMACS Model Checker in Rust
#![allow(unused_imports)]
use splr::config::Config;
use splr::solver::Solver;
use splr::traits::{SatSolverIF, ValidatorIF};
use std::env;
use std::fs::File;
use std::io::{stdin, BufRead, BufReader};
use std::path::{Path, PathBuf};
use structopt::StructOpt;

#[derive(StructOpt)]
#[structopt(
    name = "dmcr",
    about = "DIMACS-format Model Checker in Rust, version 0.0.2"
)]
struct TargetOpts {
    #[structopt(parse(from_os_str))]
    #[structopt(short = "a", long = "assign")]
    assign: Option<std::path::PathBuf>,
    #[structopt(parse(from_os_str))]
    problem: std::path::PathBuf,
}

fn main() {
    let mut found = false;
    let mut args = TargetOpts::from_args();
    let (mut s, _cnf) = Solver::build(Config::default(), &args.problem.to_str().unwrap());
    if args.assign == None {
        args.assign = Some(PathBuf::from(format!(
            ".ans_{}",
            args.problem.to_str().unwrap()
        )));
    }
    if let Some(f) = &args.assign {
        if let Ok(d) = File::open(f.as_path()) {
            s.inject_assigmnent(&read_assignment(&mut BufReader::new(d)));
            found = true;
        }
    }
    if !found {
        s.inject_assigmnent(&read_assignment(&mut BufReader::new(stdin())));
    }
    match s.validate() {
        Some(v) => println!(
            "Invalid assignment for {} due to {:?}.",
            args.problem.to_str().unwrap(),
            v
        ),
        None if found => println!(
            "Valid assignment for {} found in {}.",
            &args.problem.to_str().unwrap(),
            &args.assign.unwrap().to_str().unwrap(),
        ),
        None => println!("Valid assignment for {}.", &args.problem.to_str().unwrap()),
    }
}

fn read_assignment(rs: &mut BufRead) -> Vec<i32> {
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

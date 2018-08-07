#![allow(dead_code)]
#![allow(unused_imports)]

extern crate splr;
use splr::clause::*;
use splr::search::*;
use splr::solver::*;
use splr::types::*;
use std::io::*;
use std::io::{BufReader, Read};
use std::result::Result;
use std::{fs, mem};

fn to_pnum(v: Vec<u8>) -> i32 {
    let mut a: i32 = 0;
    for d in v {
        a *= 10;
        a += (d as i32) - 48;
    }
    a
}

fn to_mnum(v: Vec<u8>) -> i32 {
    let mut a: i32 = 0;
    for d in v {
        a *= 10;
        a += (d as i32) - 48;
    }
    0 - a
}

fn main() {
    println!("Hello, world!");
    let mut rs = BufReader::new(fs::File::open("uf8.cnf").unwrap());
    let mut buf = String::new();
    let mut nv: usize = 0;
    let mut nc: usize = 0;
    loop {
        buf.clear();
        match rs.read_line(&mut buf) {
            Ok(0) => break,
            Ok(k) => {
                let mut iter = buf.split_whitespace();
                if iter.next() == Some("p") && iter.next() == Some("cnf") {
                    if let Some(v) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                        if let Some(c) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                            nv = v;
                            nc = c;
                            break;
                        }
                    }
                }
                continue;
            }
            Err(e) => panic!("{}", e),
        }
    }
    println!("nv = {}, nc = {}", nv, nc);
    let cnf = CNFDescription {
        num_of_variables: nv,
        num_of_clauses: nc,
        pathname: "".to_string(),
    };
    let mut s: Solver = Solver::new(DEFAULT_CONFIGURATION, &cnf);
    let x: Lit = int2lit(4);
    let c1 = Clause::new(vec![int2lit(1), int2lit(2), int2lit(3)]);
    let mut c2 = Clause::new(vec![int2lit(-1), int2lit(4)]);
    let mut e = Ema::new(1000);
    for _ in 1..20 {
        e.update(0.2);
    }
    c2.activity = e.get();
    println!("# Literal: L{} -> I{}", x, x.int());
    println!(
        "# Clause: {}, {:?}, {}",
        c1,
        [c1 == c1, c2 == c2, c1 == c2],
        c2.activity
    );
    loop {
        buf.clear();
        match rs.read_line(&mut buf) {
            Ok(0) => break,
            Ok(k) => {
                let mut iter = buf.split_whitespace();
                let mut v: Vec<Lit> = Vec::new();
                for s in iter {
                    if let Ok(val) = s.parse::<i32>() {
                        if val == 0 {
                            continue;
                        } else {
                            v.push(int2lit(val));
                        }
                    }
                }
                println!("a new clause: {:?}", v);
                s.inject(false, Clause::new(v));
            }
            Err(e) => panic!("{}", e),
        }
    }

    println!("# Solver");
    println!(" - vars:  {:?}", s.vars);
    println!(" - watches: {:?}", s.watches);
    match s.solve() {
        Ok(_) => println!("OK"),
        Err(_) => println!("Failed"),
    }
    println!("nclauses = {}", s.num_clauses());
    s.learnts.pop();
    println!("# End of program");
}

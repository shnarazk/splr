#![allow(dead_code)]
#![allow(unused_imports)]

extern crate splr;
use splr::clause::*;
use splr::search::*;
use splr::solver::*;
use splr::types::*;
use std::env;
use std::io::*;
use std::io::{BufReader, Read};
use std::result::Result;
use std::{fs, mem};

fn build_solver(path: &str) -> (Solver, CNFDescription) {
    let mut rs = BufReader::new(fs::File::open(path).unwrap());
    let mut buf = String::new();
    let mut nv: usize = 0;
    let mut nc: usize = 0;
    loop {
        buf.clear();
        match rs.read_line(&mut buf) {
            Ok(0) => break,
            Ok(_k) => {
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
    let cnf = CNFDescription {
        num_of_variables: nv,
        num_of_clauses: nc,
        pathname: "".to_string(),
    };
    println!(" - desc: {}", cnf);
    let mut s: Solver = Solver::new(DEFAULT_CONFIGURATION, &cnf);
    loop {
        buf.clear();
        match rs.read_line(&mut buf) {
            Ok(0) => break,
            Ok(_k) => {
                let mut iter = buf.split_whitespace();
                let mut v: Vec<Lit> = Vec::new();
                for s in iter {
                    if let Ok(val) = s.parse::<i32>() {
                        if val == 0 {
                            if v.is_empty() {
                                println!("finish reading a cnf");
                            }
                            continue;
                        } else {
                            v.push(int2lit(val));
                        }
                    }
                }
                if v.len() != 0 {
                    v.sort();
                    s.inject(false, Clause::new(v));
                }
            }
            Err(e) => panic!("{}", e),
        }
    }
    if nc != s.num_clauses() {
        panic!("The number of clauses is inconsistent with the header.")
    }
    // println!(" - vars:  {:?}", s.vars);
    // println!(" - clauses: {:?}", s.clauses);
    // println!(" - learnts: {:?}", s.learnts);
    // println!(" - var_order: {:?}", s.var_order);
    // println!(
    //     " - assign: {:?}",
    //     s.vars.iter().map(|v| v.assign).collect::<Vec<Lbool>>()
    // );
    //for (i, w) in s.watches.iter().enumerate() {
    //    if !w.is_empty() {
    //        println!(" - watches[{:>3}] => {:?}", (i as Lit).int(), w);
    //    }
    //}
    assert_eq!(s.vars.len() - 1, cnf.num_of_variables);
    assert_eq!(s.clauses.len() - 1, cnf.num_of_clauses);
    // println!(" - solver: {:?}", s);
    (s, cnf)
}

fn main() {
    // println!("CARGO_MANIFEST_DIR = {}", env!("CARGO_MANIFEST_DIR"));
    // let target: String = env!("CARGO_MANIFEST_DIR").to_string() + "/uf100-011.cnf";
    let mut target: String = env!("CARGO_MANIFEST_DIR").to_string() + "/uf200-020.cnf";
    // let target: String = env!("CARGO_MANIFEST_DIR").to_string() + "/uf10.cnf";
    // let target: String = env!("CARGO_MANIFEST_DIR").to_string() + "/uf12.cnf";
    if let Some(f) = env::args().last() {
        target = f;
    }
    println!("Hello, world! {}", target);
    let (mut s, _cnf) = build_solver(&target);
    match s.solve() {
        Ok(s) => println!("OK {:?}", s),
        Err(e) => println!("Failed {:?}", e),
    }
    println!("# End of program");
}

fn main_() {
    println!("Hello, world!");
    println!("CARGO_MANIFEST_DIR = {}", env!("CARGO_MANIFEST_DIR"));
    let mut rs = BufReader::new(
        fs::File::open(env!("CARGO_MANIFEST_DIR").to_string() + "/uf8.cnf").unwrap(),
    );
    let mut buf = String::new();
    let mut nv: usize = 0;
    let mut nc: usize = 0;
    loop {
        buf.clear();
        match rs.read_line(&mut buf) {
            Ok(0) => break,
            Ok(_k) => {
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
            Ok(_k) => {
                let mut iter = buf.split_whitespace();
                let mut v: Vec<Lit> = Vec::new();
                for s in iter {
                    if let Ok(val) = s.parse::<i32>() {
                        if val == 0 {
                            println!("finish reading a cnf");
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
        Ok(s) => println!("OK {:?}", s),
        Err(e) => println!("Failed {:?}", e),
    }
    println!("nclauses = {}", s.num_clauses());
    println!("nlearnts = {}", s.num_learnts());
    s.clauses.pop();
    println!("# End of program");
}

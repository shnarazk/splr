extern crate splr;
use splr::clause::ClauseKind;
use splr::solver::{Certificate, SatSolver, Solver, Stat};
use splr::types::EmaKind;
use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

const VERSION: &str = "Splr-0.0.9 (Technical Preview 9) by shnarazk@gitlab.com";

fn main() {
    let mut target: Option<String> = None;
    let args: Vec<String> = env::args().skip(1).collect();
    for arg in &args {
        match arg {
            _ if arg == "--version" => {
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
        let file = Path::new(&path);
        let (mut s, _cnf) = Solver::build(&path);
        let result = format!(".ans_{}", file.file_name().unwrap().to_str().unwrap());
        match s.solve() {
            Ok(Certificate::SAT(v)) => {
                if let Ok(mut out) = File::create(&result) {
                    let mut buf = BufWriter::new(out);
                    for x in &v {
                        if let Err(why) = buf.write(format!("{} ", x).as_bytes()) {
                            panic!("failed to save: {:?}!", why);
                        }
                    }
                    if let Err(why) = buf.write(b"0\n") {
                        panic!("failed to save: {:?}!", why);
                    }
                }
                report_stat(&s);
                println!("SATISFIABLE. The answer was dumped to {}.", result.as_str());
                // println!("{:?}", v);
            }
            Ok(Certificate::UNSAT(_)) => {
                if let Ok(mut out) = File::create(&result) {
                    if let Err(why) = out.write_all(b"[]\n") {
                        panic!("failed to save: {:?}!", why);
                    }
                }
                report_stat(&s);
                println!("UNSAT, The answer was dumped to {}.", result.as_str());
                println!("[]");
            }
            Err(e) => println!("Failed {:?}", e),
        }
    }
}

fn report_stat(s: &Solver) -> () {
    println!(
        "backjump:{}, block:{}, restart:{}, reduction:{}, clauses:{}, learnts:{}",
        s.stat[Stat::Conflict as usize],
        s.stat[Stat::BlockRestart as usize],
        s.stat[Stat::Restart as usize],
        s.stat[Stat::Reduction as usize],
        s.cp[ClauseKind::Permanent as usize].head.len(),
        s.cp[ClauseKind::Removable as usize].head.len(),
    );
    println!(
        "EMA:: Asg (s:{:>.2}, f:{:>.2}), LBD (s:{:>.2}, f:{:>.2}), DL (conflict:{:>.2}, backjump:{:>.2})",
        s.ema_asg.slow, s.ema_asg.fast, s.ema_lbd.slow, s.ema_lbd.fast,
        s.c_lvl.get(), s.b_lvl.get(),
    );
}

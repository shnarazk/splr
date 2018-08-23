extern crate splr;
use splr::clause::ClauseKind;
use splr::solver::{Certificate, SatSolver, Solver, Stat};
use splr::types::EmaKind;
use std::env;

const VERSION: &str = "Splr 0.0.1 No Id, A single storage";

fn main() {
    // println!("splr 0.0.1 CARGO_MANIFEST_DIR = {}", env!("CARGO_MANIFEST_DIR"));
    // Some(env!("CARGO_MANIFEST_DIR").to_string() + "/uf200-020.cnf");
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
        let (mut s, _cnf) = Solver::build(&path);
        match s.solve() {
            Ok(Certificate::SAT(v)) => {
                report_stat(&s);
                println!("{:?}", v);
            }
            Ok(Certificate::UNSAT(v)) => println!("UNSAT {:?}", v),
            Err(e) => println!("Failed {:?}", e),
        }
    }
}

fn report_stat(s: &Solver) -> () {
    println!(
        "backjump:{}, block:{}, restart:{}, reduction:{}, clauses:{}, learnts:{}",
        s.stats[Stat::NumOfBackjump as usize],
        s.stats[Stat::NumOfBlockRestart as usize],
        s.stats[Stat::NumOfRestart as usize],
        s.stats[Stat::NumOfReduction as usize],
        s.cp[ClauseKind::Permanent as usize].clauses.len(),
        s.cp[ClauseKind::Removable as usize].clauses.len(),
    );
    println!(
        "EMA:: Asg (s:{:>.2}, f:{:>.2}), LBD (s:{:>.2}, f:{:>.2}), DL (conflict:{:>.2}, backjump:{:>.2})",
        s.ema_asg.slow, s.ema_asg.fast, s.ema_lbd.slow, s.ema_lbd.fast,
        s.c_lvl.get(), s.b_lvl.get(),
    );
}

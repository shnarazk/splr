extern crate splr;
use splr::solver::{Certificate, SatSolver, Solver, Stat};
use std::env;

fn main() {
    // println!("splr 0.0.1 CARGO_MANIFEST_DIR = {}", env!("CARGO_MANIFEST_DIR"));
    // Some(env!("CARGO_MANIFEST_DIR").to_string() + "/uf200-020.cnf");
    let mut target: Option<String> = None;
    let args: Vec<String> = env::args().skip(1).collect();
    for arg in &args {
        match arg {
            _ if arg.to_string() == "--version" => {
                println!("Splr 0.0.1");
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
            Ok(Certificate::SAT(v)) => println!("{:?}", v),
            Ok(Certificate::UNSAT(v)) => println!("UNSAT {:?}", v),
            Err(e) => println!("Failed {:?}", e),
        }
        println!(
            "backjump:{}, block:{}, restart:{}, reduction:{}, clauses:{}, learnts:{}",
            s.stats[Stat::NumOfBackjump as usize],
            s.stats[Stat::NumOfBlockRestart as usize],
            s.stats[Stat::NumOfRestart as usize],
            s.stats[Stat::NumOfReduction as usize],
            s.fixed_len,
            s.clauses.len() - s.fixed_len,
        );
        println!(
            "Ema_Asg:(s{}, f{}), Ema-LBD:(s{}, f{})",
            s.ema_asg.slow, s.ema_asg.fast, s.ema_lbd.slow, s.ema_lbd.fast,
        );
    }
}

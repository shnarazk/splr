// SAT solver for Propositional Logic in Rust
// Version 0.0.13 (Technology Preview 13)

use splr::config::Config;
use splr::solver::{Certificate, Solver};
use splr::state::*;
use splr::traits::SatSolverIF;
use std::fs::File;
use std::io::{BufWriter, Write};
use structopt::StructOpt;

#[derive(StructOpt)]
#[structopt(
    name = "splr",
    about = "SAT solver for Propositional Logic in Rust, Technology Preview 13"
)]
struct CLOpts {
    /// EMA coefficient for number of assignments
    #[structopt(long = "ra", default_value = "3500")]
    restart_asg_samples: usize,
    /// EMA coefficient for learnt clause LBD
    #[structopt(long = "rl", default_value = "50")]
    restart_lbd_samples: usize,
    /// K in Glucose, for restart
    #[structopt(long = "rt", default_value = "0.60")]
    restart_threshold: f64,
    /// R in Glucose, for blocking
    #[structopt(long = "rb", default_value = "1.40")]
    restart_blocking: f64,
    /// Minimal stpes between restart
    #[structopt(long = "rs", default_value = "50")]
    restart_step: usize,
    /// Uses another format for progress report
    #[structopt(long = "--log", short = "l")]
    use_log: bool,
    /// Disables clause/variable elimination
    #[structopt(long = "no-elim", short = "e")]
    no_elim: bool,
    /// Disables dynamic strategy adaptation
    #[structopt(long = "no-adaptation", short = "a")]
    no_adapt: bool,
    /// a CNF file to solve
    #[structopt(parse(from_os_str))]
    cnf: std::path::PathBuf,
}

fn main() {
    let args = CLOpts::from_args();
    if args.cnf.exists() {
        let mut config = Config::default();
        config.adapt_strategy = !args.no_adapt;
        config.restart_thr = args.restart_threshold;
        config.restart_blk = args.restart_blocking;
        config.restart_asg_len = args.restart_asg_samples;
        config.restart_lbd_len = args.restart_lbd_samples;
        config.restart_step = args.restart_step;
        config.progress_log = args.use_log;
        if args.no_elim {
            config.use_elim = false;
        }
        let (mut s, _cnf) = Solver::build(config, &args.cnf.to_str().unwrap());
        let result = format!(".ans_{}", args.cnf.file_name().unwrap().to_str().unwrap());
        match s.solve() {
            Ok(Certificate::SAT(v)) => {
                if let Ok(out) = File::create(&result) {
                    let mut buf = BufWriter::new(out);
                    if let Err(why) = (|| {
                        buf.write_all(
                            format!(
                                "c generated by splr-tp13 for {}\n",
                                args.cnf.to_str().unwrap(),
                            )
                            .as_bytes(),
                        )?;
                        report(&s.state, &mut buf)?;
                        for x in &v {
                            buf.write_all(format!("{} ", x).as_bytes())?;
                        }
                        buf.write(b"0\n")
                    })() {
                        panic!("failed to save: {:?}!", why);
                    }
                }
                println!(
                    "SATISFIABLE: {}. The answer was dumped to {}.",
                    s.state.target.pathname,
                    result.as_str()
                );
            }
            Ok(Certificate::UNSAT(_)) => {
                if let Ok(out) = File::create(&result) {
                    let mut buf = BufWriter::new(out);
                    if let Err(why) = (|| {
                        buf.write_all(
                            format!(
                                "c generated by splr-tp13 for {}\n",
                                args.cnf.to_str().unwrap(),
                            )
                            .as_bytes(),
                        )?;
                        report(&s.state, &mut buf)?;
                        buf.write_all(b"0\n")
                    })() {
                        panic!("failed to save: {:?}!", why);
                    }
                }
                println!(
                    "UNSAT: {}, The answer was dumped to {}.",
                    s.state.target.pathname,
                    result.as_str()
                );
            }
            Err(_) => println!("Failed"),
        }
    } else {
        println!(
            "{} does not exist.",
            args.cnf.file_name().unwrap().to_str().unwrap()
        );
    }
}

fn report<W: Write>(state: &State, out: &mut BufWriter<W>) -> std::io::Result<()> {
    out.write_all(format!("c {}, Mode:{:>9}\n", state, "solved").as_bytes())?;
    out.write_all(
        format!(
            "c  #conflict:{}, #decision:{}, #propagate:{} \n",
            format!("{:>11}", state.dumper.vali[LogUsizeId::Conflict as usize]),
            format!("{:>13}", state.dumper.vali[LogUsizeId::Decision as usize]),
            format!("{:>15}", state.dumper.vali[LogUsizeId::Propagate as usize]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c   Assignment|#rem:{}, #fix:{}, #elm:{}, prg%:{} \n",
            format!("{:>9}", state.dumper.vali[LogUsizeId::Remain as usize]),
            format!("{:>9}", state.dumper.vali[LogUsizeId::Fixed as usize]),
            format!("{:>9}", state.dumper.vali[LogUsizeId::Eliminated as usize]),
            format!("{:>9.4}", state.dumper.valf[LogF64Id::Progress as usize]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c  Clause Kind|Remv:{}, LBD2:{}, Binc:{}, Perm:{} \n",
            format!("{:>9}", state.dumper.vali[LogUsizeId::Removable as usize]),
            format!("{:>9}", state.dumper.vali[LogUsizeId::LBD2 as usize]),
            format!("{:>9}", state.dumper.vali[LogUsizeId::Binclause as usize]),
            format!("{:>9}", state.dumper.vali[LogUsizeId::Permanent as usize]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c      Restart|#BLK:{}, #RST:{}, eASG:{}, eLBD:{} \n",
            format!(
                "{:>9}",
                state.dumper.vali[LogUsizeId::RestartBlock as usize]
            ),
            format!("{:>9}", state.dumper.vali[LogUsizeId::Restart as usize]),
            format!("{:>9.4}", state.dumper.valf[LogF64Id::EmaAsg as usize]),
            format!("{:>9.4}", state.dumper.valf[LogF64Id::EmaLBD as usize]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c    Conflicts|aLBD:{}, bjmp:{}, cnfl:{} |blkR:{} \n",
            format!("{:>9.2}", state.dumper.valf[LogF64Id::AveLBD as usize]),
            format!("{:>9.2}", state.dumper.valf[LogF64Id::BLevel as usize]),
            format!("{:>9.2}", state.dumper.valf[LogF64Id::CLevel as usize]),
            format!("{:>9.4}", state.dumper.valf[LogF64Id::RestartBlkR as usize]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c    Clause DB|#rdc:{}, #smp:{}, #elm:{} |frcK:{} \n",
            format!("{:>9}", state.dumper.vali[LogUsizeId::Reduction as usize]),
            format!(
                "{:>9}",
                state.dumper.vali[LogUsizeId::Simplification as usize]
            ),
            format!("{:>9}", state.dumper.vali[LogUsizeId::Elimination as usize]),
            format!("{:>9.4}", state.dumper.valf[LogF64Id::RestartThrK as usize]),
        )
        .as_bytes(),
    )?;
    out.write_all(b"c\n")?;
    Ok(())
}

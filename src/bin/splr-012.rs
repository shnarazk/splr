// SAT solver for Propositional Logic in Rust

use splr::clause::CertifiedRecord;
use splr::config::{Config, VERSION};
use splr::solver::{Certificate, Solver};
use splr::state::*;
use splr::traits::SatSolverIF;
use std::fs::File;
use std::io::{BufWriter, Write};
use structopt::StructOpt;

fn main() {
    let config = Config::from_args();
    if !config.cnf_file.exists() {
        println!(
            "{} does not exist.",
            config.cnf_file.file_name().unwrap().to_str().unwrap()
        );
        return;
    }
    let input = config.cnf_file.to_str().unwrap().to_string();
    let result = if config.output_filname != "" {
        config.output_filname.to_string()
    } else {
        format!(
            ".ans_{}",
            config
                .cnf_file
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .to_string()
        )
    };
    let mut s = Solver::build(&config).expect("failed to load");
    match s.solve() {
        Ok(Certificate::SAT(v)) => {
            if let Ok(out) = File::create(&result) {
                let mut buf = BufWriter::new(out);
                if let Err(why) = (|| {
                    buf.write_all(
                        format!(
                            "c An assignment set generated by splr-{} for {}\nc\n",
                            VERSION, input,
                        )
                        .as_bytes(),
                    )?;
                    report(&s.state, &mut buf)?;
                    buf.write_all(b"s SATISFIABLE\n")?;
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
        Ok(Certificate::UNSAT) => {
            if let Ok(out) = File::create(&result) {
                let mut buf = BufWriter::new(out);
                if let Err(why) = (|| {
                    buf.write_all(
                        format!(
                            "c The empty assignment set generated by splr-{} for {}\nc\n",
                            VERSION, input,
                        )
                        .as_bytes(),
                    )?;
                    report(&s.state, &mut buf)?;
                    buf.write_all(b"s UNSATISFIABLE\n")?;
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
            if !config.use_certification {
                return;
            }
            if let Ok(out) = File::create(&config.proof_filename) {
                let mut buf = BufWriter::new(out);
                if let Err(why) = (|| {
                    buf.write_all(
                        format!("c Proof generated by splr-{} for {}\nc\n", VERSION, input,)
                            .as_bytes(),
                    )?;
                    buf.write_all(b"s UNSATISFIABLE\n")?;
                    for (f, x) in &s.cdb.certified[1..] {
                        if *f == CertifiedRecord::DELETE {
                            buf.write_all(b"d ")?;
                        }
                        for l in x {
                            buf.write_all(format!("{} ", l).as_bytes())?;
                        }
                        buf.write_all(b"0\n")?;
                    }
                    buf.write_all(b"0\n")
                })() {
                    panic!("failed to save: {:?}!", why);
                }
                println!("The certification was dumped to {}.", config.proof_filename,);
            }
        }
        Err(_) => println!("Failed to execution by an internal error."),
    }
}

fn report<W: Write>(state: &State, out: &mut BufWriter<W>) -> std::io::Result<()> {
    let tm = match state.start.elapsed() {
        Ok(e) => e.as_secs() as f64 + f64::from(e.subsec_millis()) / 1000.0f64,
        Err(_) => 0.0f64,
    };
    out.write_all(
        format!(
            "c {:<35}, v:{:8}, c:{:8}, time:{:9.2}\n",
            state.target.pathname, state.target.num_of_variables, state.target.num_of_clauses, tm,
        )
        .as_bytes(),
    )?;
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
            "c    Clause DB|#rdc:{}, #sce:{}, #exe:{} |frcK:{} \n",
            format!("{:>9}", state.dumper.vali[LogUsizeId::Reduction as usize]),
            format!(
                "{:>9}",
                state.dumper.vali[LogUsizeId::SatClauseElim as usize]
            ),
            format!(
                "{:>9}",
                state.dumper.vali[LogUsizeId::ExhaustiveElim as usize]
            ),
            format!("{:>9.4}", state.dumper.valf[LogF64Id::RestartThrK as usize]),
        )
        .as_bytes(),
    )?;
    out.write_all(b"c\n")?;
    Ok(())
}

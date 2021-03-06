// SAT solver for Propositional Logic in Rust
use {
    splr::{
        assign, cdb,
        config::{self, CERTIFICATION_DEFAULT_FILENAME},
        processor,
        solver::*,
        state::{self, LogF64Id, LogUsizeId},
        Config, EmaIF, PropertyDereference, PropertyReference, SolverError, VERSION,
    },
    std::{
        borrow::Cow,
        env,
        fs::File,
        io::{BufWriter, Write},
        path::PathBuf,
        thread,
        time::Duration,
    },
};

const RED: &str = "\x1B[001m\x1B[031m";
const GREEN: &str = "\x1B[001m\x1B[032m";
const BLUE: &str = "\x1B[001m\x1B[034m";
const RESET: &str = "\x1B[000m";

fn colored(v: Result<bool, &SolverError>, no_color: bool) -> Cow<'static, str> {
    if no_color {
        match v {
            Ok(false) => Cow::Borrowed("s UNSATISFIABLE"),
            Ok(true) => Cow::Borrowed("s SATISFIABLE"),
            Err(_) => Cow::Borrowed("s UNKNOWN"),
        }
    } else {
        match v {
            Ok(false) => Cow::from(format!("{}s UNSATISFIABLE{}", BLUE, RESET)),
            Ok(true) => Cow::from(format!("{}s SATISFIABLE{}", GREEN, RESET)),
            Err(_) => Cow::from(format!("{}s UNKNOWN{}", RED, RESET)),
        }
    }
}

fn main() {
    let mut config = Config::default();
    config.inject_from_args();
    config.splr_interface = true;
    if !config.cnf_file.exists() {
        println!(
            "{} does not exist.",
            config.cnf_file.file_name().unwrap().to_str().unwrap()
        );
        return;
    }
    let cnf_file = config.cnf_file.to_string_lossy();
    let ans_file: Option<PathBuf> = match config.io_rfile.to_string_lossy().as_ref() {
        "-" => None,
        "" => Some(config.io_odir.join(PathBuf::from(format!(
            "ans_{}",
            config.cnf_file.file_name().unwrap().to_string_lossy(),
        )))),
        _ => Some(config.io_odir.join(&config.io_rfile)),
    };
    if config.io_pfile.to_string_lossy() != CERTIFICATION_DEFAULT_FILENAME
        && !config.use_certification
    {
        println!("Abort: You set a proof filename with '--proof' explicitly, but didn't set '--certify'. It doesn't look good.");
        return;
    }
    if let Ok(val) = env::var("SPLR_TIMEOUT") {
        if let Ok(timeout) = val.parse::<u64>() {
            let input = cnf_file.as_ref().to_string();
            let no_color = config.no_color;
            thread::spawn(move || {
                thread::sleep(Duration::from_millis(timeout * 1000));
                println!(
                    "{} (TimeOut): {}",
                    colored(Err(&SolverError::TimeOut), no_color),
                    input
                );
                std::process::exit(0);
            });
        }
    }
    let mut s = match Solver::build(&config) {
        Err(SolverError::RootLevelConflict(_)) => {
            println!(
                "\x1B[1G\x1B[K{}: {}",
                colored(Ok(false), config.no_color),
                config.cnf_file.file_name().unwrap().to_string_lossy(),
            );
            std::process::exit(20);
        }
        Err(e) => {
            panic!("{:?}", e);
        }
        Ok(solver) => solver,
    };
    let res = s.solve();
    save_result(&mut s, &res, &cnf_file, ans_file);
    std::process::exit(match res {
        Ok(Certificate::SAT(_)) => 10,
        Ok(Certificate::UNSAT) => 20,
        Err(_) => 0,
    });
}

fn save_result<S: AsRef<str> + std::fmt::Display>(
    s: &mut Solver,
    res: &SolverResult,
    input: S,
    output: Option<PathBuf>,
) {
    let mut ofile;
    let mut otty;
    let mut redirect = false;
    let mut buf: &mut dyn Write = match output {
        Some(ref file) => {
            if let Ok(f) = File::create(file) {
                ofile = BufWriter::new(f);
                &mut ofile
            } else {
                redirect = true;
                otty = BufWriter::new(std::io::stdout());
                &mut otty
            }
        }
        None => {
            otty = BufWriter::new(std::io::stdout());
            &mut otty
        }
    };
    match res {
        Ok(Certificate::SAT(v)) => {
            match output {
                Some(ref f) if redirect && !s.state.config.quiet_mode => println!(
                    "      Result|dump: to STDOUT instead of {} due to an IO error.",
                    f.to_string_lossy(),
                ),
                Some(ref f) if !s.state.config.quiet_mode => {
                    println!("      Result|file: {}", f.to_str().unwrap(),)
                }
                _ => (),
            }
            println!("{}: {}", colored(Ok(true), s.state.config.no_color), input);
            if let Err(why) = (|| {
                buf.write_all(
                    format!(
                        "c This file was generated by splr-{} for {}\nc \n",
                        VERSION, input,
                    )
                    .as_bytes(),
                )?;
                report(s, buf)?;
                buf.write_all(b"s SATISFIABLE\nv ")?;
                for x in v {
                    buf.write_all(format!("{} ", x).as_bytes())?;
                }
                buf.write(b"0\n")
            })() {
                println!("Abort: failed to save by {}!", why);
            }
        }
        Ok(Certificate::UNSAT) => {
            match output {
                Some(ref f) if redirect && !s.state.config.quiet_mode => println!(
                    "      Result|dump: to STDOUT instead of {} due to an IO error.",
                    f.to_string_lossy(),
                ),
                Some(ref f) if !s.state.config.quiet_mode => {
                    println!("      Result|file: {}", f.to_str().unwrap(),)
                }
                _ => (),
            }
            if s.state.config.use_certification {
                s.save_certification();
                println!(
                    " Certificate|file: {}",
                    s.state.config.io_pfile.to_string_lossy()
                );
            }
            println!("{}: {}", colored(Ok(false), s.state.config.no_color), input);
            if let Err(why) = (|| {
                buf.write_all(
                    format!(
                        "c The empty assignment set generated by splr-{} for {}\nc \n",
                        VERSION, input,
                    )
                    .as_bytes(),
                )?;
                report(s, &mut buf)?;
                buf.write_all(b"s UNSATISFIABLE\n")?;
                buf.write_all(b"0\n")
            })() {
                println!("Abort: failed to save by {}!", why);
            }
        }
        Err(e) => {
            match output {
                Some(ref f) if redirect && !s.state.config.quiet_mode => println!(
                    "      Result|dump: to STDOUT instead of {} due to an IO error.",
                    f.to_string_lossy(),
                ),
                Some(ref f) if !s.state.config.quiet_mode => {
                    println!("      Result|file: {}", f.to_str().unwrap(),)
                }
                _ => (),
            }
            println!(
                "{} ({}): {}",
                colored(Err(e), s.state.config.no_color),
                e,
                input
            );
            if let Err(why) = (|| {
                buf.write_all(
                    format!(
                        "c An assignment set generated by splr-{} for {}\nc \n",
                        VERSION, input,
                    )
                    .as_bytes(),
                )?;
                report(s, buf)?;
                buf.write_all(format!("c {}\n{}\n", e, colored(Err(e), true)).as_bytes())?;
                buf.write(b"0\n")
            })() {
                println!("Abort: failed to save by {}!", why);
            }
        }
    }
}

fn report(s: &Solver, out: &mut dyn Write) -> std::io::Result<()> {
    let state = &s.state;
    let elapsed: Duration = s.state.start.elapsed();
    let tm: f64 = elapsed.as_millis() as f64 / 1_000.0;
    out.write_all(
        format!(
            "c {:<43}, #var:{:9}, #cls:{:9}\n",
            state
                .config
                .cnf_file
                .file_name()
                .map_or(Cow::from("file with strange chars"), |f| f
                    .to_string_lossy()),
            state.target.num_of_variables,
            state.target.num_of_clauses,
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c  #conflict:{}, #decision:{}, #propagate:{},\n",
            format!("{:>11}", state[LogUsizeId::NumConflict]),
            format!("{:>13}", state[LogUsizeId::NumDecision]),
            format!("{:>15}", state[LogUsizeId::NumPropagate]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c   Assignment|#rem:{}, #fix:{}, #elm:{}, prg%:{},\n",
            format!("{:>9}", state[LogUsizeId::RemainingVar]),
            format!("{:>9}", state[LogUsizeId::AssertedVar]),
            format!("{:>9}", state[LogUsizeId::EliminatedVar]),
            format!("{:>9.4}", state[LogF64Id::Progress]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c       Clause|Remv:{}, LBD2:{}, Binc:{}, Perm:{},\n",
            format!("{:>9}", state[LogUsizeId::RemovableClause]),
            format!("{:>9}", state[LogUsizeId::LBD2Clause]),
            format!("{:>9}", state[LogUsizeId::BiClause]),
            format!("{:>9}", state[LogUsizeId::PermanentClause]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c      Restart|#BLK:{}, #RST:{}, trgr:{}, peak:{},\n",
            format!("{:>9}", state[LogUsizeId::RestartBlock]),
            format!("{:>9}", state[LogUsizeId::Restart]),
            format!("{:>9}", state[LogUsizeId::RestartTriggerLevel]),
            format!("{:>9}", state[LogUsizeId::RestartTriggerLevelMax]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c          LBD|avrg:{}, trnd:{}, depG:{}, /dpc:{},\n",
            format!("{:>9.4}", state[LogF64Id::EmaLBD]),
            format!("{:>9.4}", state[LogF64Id::TrendLBD]),
            format!("{:>9.4}", state[LogF64Id::DpAverageLBD]),
            format!("{:>9.2}", state[LogF64Id::DecisionPerConflict]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c     Conflict|tASG:{}, cLvl:{}, bLvl:{}, /ppc:{},\n",
            format!("{:>9.4}", state[LogF64Id::TrendASG]),
            format!("{:>9.2}", state[LogF64Id::CLevel]),
            format!("{:>9.2}", state[LogF64Id::BLevel]),
            format!("{:>9.2}", state[LogF64Id::PropagationPerConflict]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c         misc|elim:{}, #sub:{}, core:{}, /cpr:{},\n",
            format!("{:>9}", state[LogUsizeId::Simplify]),
            format!("{:>9}", state[LogUsizeId::ClauseSubsumption]),
            format!("{:>9}", state[LogUsizeId::UnreachableCore]),
            format!("{:>9.2}", state[LogF64Id::ConflictPerRestart]),
        )
        .as_bytes(),
    )?;
    #[cfg(not(feature = "strategy_adaptation"))]
    {
        out.write_all(format!("c     Strategy|mode:  generic, time:{:9.2},\n", tm).as_bytes())?;
    }
    #[cfg(feature = "strategy_adaptation")]
    {
        out.write_all(
            format!(
                "c     Strategy|mode:{:>15}, time:{:9.2},\n",
                state.strategy.0, tm,
            )
            .as_bytes(),
        )?;
    }
    out.write_all("c\n".as_bytes())?;
    for key in &config::property::F64S {
        out.write_all(
            format!(
                "c   config::{:<27}{:>15}\n",
                format!("{:?}", key),
                s.state.config.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &assign::property::USIZES {
        out.write_all(
            format!(
                "c   assign::{:<27}{:>15}\n",
                format!("{:?}", key),
                s.asg.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &assign::property::EMAS {
        out.write_all(
            format!(
                "c   assign::{:<27}{:>19.3}\n",
                format!("{:?}", key),
                s.asg.refer(*key).get(),
            )
            .as_bytes(),
        )?;
    }
    for key in &cdb::property::USIZES {
        out.write_all(
            format!(
                "c   clause::{:<27}{:>15}\n",
                format!("{:?}", key),
                s.cdb.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &cdb::property::F64 {
        out.write_all(
            format!(
                "c   clause::{:<27}{:>19.3}\n",
                format!("{:?}", key),
                s.cdb.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &processor::property::USIZES {
        out.write_all(
            format!(
                "c   processor::{:<24}{:>15}\n",
                format!("{:?}", key),
                s.elim.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &restart::property::USIZES {
        out.write_all(
            format!(
                "c   restart::{:<26}{:>15}\n",
                format!("{:?}", key),
                s.rst.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &state::property::USIZES {
        out.write_all(
            format!(
                "c   state::{:<28}{:>15}\n",
                format!("{:?}", key),
                s.state.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &state::property::EMAS {
        out.write_all(
            format!(
                "c   state::{:<28}{:>19.3}\n",
                format!("{:?}", key),
                s.state.refer(*key).get(),
            )
            .as_bytes(),
        )?;
    }

    out.write_all(b"c \n")?;
    Ok(())
}

// SAT solver for Propositional Logic in Rust
use {
    libc::{clock_gettime, timespec, CLOCK_PROCESS_CPUTIME_ID},
    splr::{
        cdb::CertifiedRecord,
        solver::*,
        state::{LogF64Id, LogUsizeId},
        types::Export,
        Config, SolverError, VERSION,
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
    structopt::StructOpt,
};

const RED: &str = "\x1B[001m\x1B[031m";
const GREEN: &str = "\x1B[001m\x1B[032m";
const BLUE: &str = "\x1B[001m\x1B[034m";
const RESET: &str = "\x1B[000m";

fn colored(v: Result<bool, &SolverError>, quiet: bool) -> Cow<'static, str> {
    if quiet {
        match v {
            Ok(false) => Cow::Borrowed("s UNSATISFIABLE"),
            Ok(true) => Cow::Borrowed("s SATISFIABLE"),
            Err(_) => Cow::Borrowed("s UNKNOWN"),
        }
    } else {
        match v {
            Ok(false) => Cow::from(format!("{}s UNSATISFIABLE{}", GREEN, RESET)),
            Ok(true) => Cow::from(format!("{}s SATISFIABLE{}", BLUE, RESET)),
            Err(_) => Cow::from(format!("{}s UNKNOWN{}", RED, RESET)),
        }
    }
}

fn main() {
    /*
    let args = &[
        Argument::new(
            &[''],
            &["ADP"],
            Some("Strategy adaptation switch"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["ELI"],
            Some("Eliminator switch"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["RPH"],
            Some("Eliminator switch"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["RSR"],
            Some("Reason-Side Rewarding switch"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["STB"],
            Some("Stabilization switch"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["RDR"],
            Some("Clause reduction switch"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["VIV"],
            Some("Vivification switch"),
            DataType::Text,
        ).unwrap(),

        //
        //## solver configuration
        //
        Argument::new(
            &[],
            &["cbt"],
            Some("Dec. lvl to use chronoBT"),
            DataType::Text,
        ).unwrap(),

        Argument::new(
            &[],
            &["cl"],
            Some("Soft limit of #clauses (6MC/GB)"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["ii"],
            Some("#cls to start in-processor"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &[""],
            Some(""),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &['t'],
            &["timeout"],
            Some("CPU time limit in sec."),
            DataType::Text,
        ).unwrap(),

        //
        //## I/O configuration
        //
        Argument::new(
            &[],
            &["stat"],
            Some("Interval for dumping stat data"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &['o'],
            &["dir"],
            Some("Output directory"),
            DataType::Files,
        ).unwrap(),
        Argument::new(
            &[],
            &[""],
            Some(""),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["proof"],
            Some("DRAT Cert. filename"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &['r'],
            &["result"],
            Some("Result filename/stdout"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &['C'],
            &["no-color"],
            Some("Disable coloring"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &['q'],
            &["quiet"],
            Some("Disable any progress message"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &[""],
            Some(""),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &['c'],
            &["certify"],
            Some("Writes a DRAT UNSAT certification file"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &['l'],
            &["log"],
            Some("Uses Glucose-like progress report"),
            DataType::Text,
        ).unwrap(),

        //
        //## eliminator
        //
        Argument::new(
            &[],
            &["ecl"],
            Some("Max #lit for clause subsume"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["evl"],
            Some("Grow limit of #cls in var elim."),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["evo"],
            Some("Max #cls for var elimination"),
            DataType::Text,
        ).unwrap(),

        //
        //## restarter
        //
        Argument::new(
            &[],
            &["rs"],
            Some("#conflicts between restarts"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["ral"],
            Some("Length of assign. fast EMA"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["ras"],
            Some("Length of assign. slow EMA"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["rat"],
            Some("Blocking restart threshold"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["rct"],
            Some("Conflict Correlation threshold"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["rll"],
            Some("Length of LBD fast EMA"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["rls"],
            Some("Length of LBD slow EMA"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["rlt"],
            Some("Forcing restart threshold"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["rut"],
            Some("Usability to restart"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["rss"],
            Some("Stabilizer scaling"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["vib"],
            Some("Lower bound of vivif. loop"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["vie"],
            Some("Upper bound of vivif. loop"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["vii"],
            Some("Vivification interval"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["vis"],
            Some("#reduction for next vivif."),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["vri"],
            Some("Initial var reward decay"),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &[""],
            Some(""),
            DataType::Text,
        ).unwrap(),
        Argument::new(
            &[],
            &["vrm"],
            Some("Maximum var reward decay"),
            DataType::Text,
        ).unwrap(),
    ];
    */
    let mut config = Config::from_args().override_args();
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
            ".ans_{}",
            config.cnf_file.file_name().unwrap().to_string_lossy(),
        )))),
        _ => Some(config.io_odir.join(&config.io_rfile)),
    };
    if config.io_pfile.to_string_lossy() != "proof.out" && !config.use_certification {
        println!("Abort: You set a proof filename with '--proof' explicitly, but didn't set '--certify'. It doesn't look good.");
        return;
    }
    if let Ok(val) = env::var("SPLR_TIMEOUT") {
        if let Ok(timeout) = val.parse::<u64>() {
            let input = cnf_file.as_ref().to_string();
            let quiet_mode = config.quiet_mode;
            thread::spawn(move || {
                thread::sleep(Duration::from_millis(timeout * 1000));
                println!(
                    "{} (TimeOut): {}",
                    colored(Err(&SolverError::TimeOut), quiet_mode),
                    input
                );
                std::process::exit(0);
            });
        }
    }
    let mut s = Solver::build(&config).expect("failed to load");
    let res = s.solve();
    save_result(&s, &res, &cnf_file, ans_file);
    if 0 < s.state.config.io_dump && !s.state.development.is_empty() {
        let dump = config.cnf_file.file_stem().unwrap().to_str().unwrap();
        if let Ok(f) = File::create(format!("stat_{}.csv", dump)) {
            let mut buf = BufWriter::new(f);
            buf.write_all(b"conflict,asserted,restart,block,ASG,LBD\n")
                .unwrap();
            for (n, a, b, c, d, e) in s.state.development.iter() {
                buf.write_all(
                    format!("{:.0},{:.5},{:.0},{:.0},{:.5},{:.5}\n", n, a, b, c, d, e,).as_bytes(),
                )
                .unwrap();
            }
        }
    }
    std::process::exit(match res {
        Ok(Certificate::SAT(_)) => 10,
        Ok(Certificate::UNSAT) => 20,
        Err(_) => 0,
    });
}

fn save_result<S: AsRef<str> + std::fmt::Display>(
    s: &Solver,
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
                Some(ref f) if redirect => println!(
                    "      Result|dump: to STDOUT instead of {} due to an IO error.",
                    f.to_string_lossy(),
                ),
                Some(ref f) => println!("      Result|file: {}", f.to_str().unwrap(),),
                _ => (),
            }
            println!(
                "{}: {}",
                colored(Ok(true), s.state.config.quiet_mode),
                input
            );
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
                Some(ref f) if redirect => println!(
                    "      Result|dump: to STDOUT instead of {} due to an IO error.",
                    f.to_string_lossy(),
                ),
                Some(ref f) => println!("      Result|file: {}", f.to_str().unwrap(),),
                _ => (),
            }
            if s.state.config.use_certification {
                let proof_file: PathBuf = s.state.config.io_odir.join(&s.state.config.io_pfile);
                save_proof(&s, &input, &proof_file);
                println!(
                    " Certificate|file: {}",
                    s.state.config.io_pfile.to_string_lossy()
                );
            }
            println!(
                "{}: {}",
                colored(Ok(false), s.state.config.quiet_mode),
                input
            );
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
                Some(ref f) if redirect => println!(
                    "      Result|dump: to STDOUT instead of {} due to an IO error.",
                    f.to_string_lossy(),
                ),
                Some(ref f) => println!("      Result|file: {}", f.to_str().unwrap(),),
                _ => (),
            }
            println!(
                "{} ({}): {}",
                colored(Err(e), s.state.config.quiet_mode),
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

fn save_proof<S: AsRef<str> + std::fmt::Display>(s: &Solver, input: S, output: &PathBuf) {
    let mut buf = match File::create(output) {
        Ok(out) => BufWriter::new(out),
        Err(e) => {
            println!(
                "Abort: failed to create the proof file {:?} by {}!",
                output.to_string_lossy(),
                e
            );
            return;
        }
    };
    if let Err(why) = (|| {
        buf.write_all(
            format!("c Proof generated by splr-{} for {}\nc \n", VERSION, input).as_bytes(),
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
        println!(
            "Abort: failed to save to {} by {}!",
            output.to_string_lossy(),
            why
        );
        return;
    }
}

fn report(s: &Solver, out: &mut dyn Write) -> std::io::Result<()> {
    let state = &s.state;
    let tm = {
        let mut time = timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        if unsafe { clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &mut time) } == -1 {
            match state.start.elapsed() {
                Ok(e) => e.as_secs() as f64 + f64::from(e.subsec_millis()) / 1000.0f64,
                Err(_) => 0.0f64,
            }
        } else {
            time.tv_sec as f64 + time.tv_nsec as f64 / 1_000_000_000.0f64
        }
    };
    out.write_all(
        format!(
            "c {:<43}, #var:{:9}, #cls:{:9}\n",
            state.target.pathname, state.target.num_of_variables, state.target.num_of_clauses,
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c  #conflict:{}, #decision:{}, #propagate:{},\n",
            format!("{:>11}", state[LogUsizeId::Conflict]),
            format!("{:>13}", state[LogUsizeId::Decision]),
            format!("{:>15}", state[LogUsizeId::Propagate]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c   Assignment|#rem:{}, #fix:{}, #elm:{}, prg%:{},\n",
            format!("{:>9}", state[LogUsizeId::Remain]),
            format!("{:>9}", state[LogUsizeId::Assert]),
            format!("{:>9}", state[LogUsizeId::Eliminated]),
            format!("{:>9.4}", state[LogF64Id::Progress]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c       Clause|Remv:{}, LBD2:{}, Binc:{}, Perm:{},\n",
            format!("{:>9}", state[LogUsizeId::Removable]),
            format!("{:>9}", state[LogUsizeId::LBD2]),
            format!("{:>9}", state[LogUsizeId::Binclause]),
            format!("{:>9}", state[LogUsizeId::Permanent]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c  {}|#RST:{}, #BLK:{}, #STB:{}, #CNC:{},\n",
            if s.rst.mode().0 == RestartMode::Luby {
                "LubyRestart"
            } else {
                "    Restart"
            },
            format!("{:>9}", state[LogUsizeId::Restart]),
            format!("{:>9}", state[LogUsizeId::RestartBlock]),
            format!("{:>9}", state[LogUsizeId::Stabilize]),
            format!("{:>9}", state[LogUsizeId::RestartCancel]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c          EMA|tLBD:{}, tASG:{}, eMLD:{}, eCCC:{},\n",
            format!("{:>9.4}", state[LogF64Id::TrendLBD]),
            format!("{:>9.4}", state[LogF64Id::TrendASG]),
            format!("{:>9.4}", state[LogF64Id::EmaMLD]),
            format!("{:>9.0}", state[LogF64Id::EmaCCC]),
        )
        .as_bytes(),
    )?;

    out.write_all(
        format!(
            "c     Conflict|eLBD:{}, cnfl:{}, bjmp:{}, /ppc:{},\n",
            format!("{:>9.2}", state[LogF64Id::EmaLBD]),
            format!("{:>9.2}", state[LogF64Id::CLevel]),
            format!("{:>9.2}", state[LogF64Id::BLevel]),
            format!("{:>9.4}", state[LogF64Id::PropagationPerConflict]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c         misc|elim:{}, cviv:{}, #vbv:{}, /cpr:{},\n",
            format!("{:>9}", state[LogUsizeId::Simplify]),
            format!("{:>9}", state[LogUsizeId::Vivify]),
            format!("{:>9}", state[LogUsizeId::VivifiedVar]),
            format!("{:>9.2}", state[LogF64Id::ConflictPerRestart]),
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c     Strategy|mode:{:>15}, time:{:9.2},\n",
            state.strategy.0, tm,
        )
        .as_bytes(),
    )?;
    out.write_all(b"c \n")?;
    Ok(())
}

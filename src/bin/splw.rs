#[allow(unused_imports)]
use {
    crossterm::{
        event::{self, Event, KeyCode, KeyEventKind},
        execute,
        terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
    },
    ratatui::{
        layout::{Direction, Layout},
        prelude::*,
        style::Color,
        // symbols::border,
        widgets::{block::*, *},
    },
    splr::{
        assign, cdb,
        config::{self, CERTIFICATION_DEFAULT_FILENAME},
        solver::Solver as Splr,
        solver::{Certificate, SatSolverIF, SearchState, SolveIF, SolverResult},
        state::{self, LogF64Id, LogUsizeId},
        Config, EmaIF, PropertyDereference, PropertyReference, SolverError, VERSION,
    },
    std::{
        borrow::Cow,
        env,
        error::Error,
        fs::File,
        io,
        path::PathBuf,
        thread,
        time::{Duration, Instant},
    },
};

#[derive(Debug)]
pub struct App {
    solver: Splr,
    state: SearchState,
    counter: i16,
    asg_stats: [u64; 4],
    #[allow(dead_code)]
    start: Instant,
}

impl App {
    fn solver(solver: Splr, state: SearchState) -> Self {
        App {
            solver,
            state,
            counter: 0,
            asg_stats: [0; 4],
            start: Instant::now(),
        }
    }
    fn run<B: Backend>(&mut self, terminal: &mut Terminal<B>) -> Result<(), Box<dyn Error>> {
        macro_rules! scaling {
            ($n: expr) => {
                (($n.max(1) as f64).log2() * 10.0) as u64
            };
        }
        let timeout = Duration::from_millis(0);
        loop {
            self.counter += 1;
            let ret: Result<Option<bool>, SolverError> = {
                let App {
                    ref mut solver,
                    state: ref mut ss,
                    ..
                } = self;
                solver.search_stage(ss)
            };
            self.asg_stats[0] = scaling!(self.state.current_core());
            self.asg_stats[1] = scaling!(self
                .solver
                .asg
                .derefer(splr::assign::property::Tusize::NumAssertedVar));
            self.asg_stats[2] = scaling!(self
                .solver
                .asg
                .derefer(splr::assign::property::Tusize::NumEliminatedVar));
            terminal.draw(|f| self.render_frame(f))?;
            match ret {
                Ok(None) => {
                    if crossterm::event::poll(timeout)? && self.handle_events()? {
                        return Ok(());
                    }
                }
                Ok(Some(sat)) => {
                    if self.solver.postprocess(Ok(sat)).is_ok() {
                        return Ok(());
                    } else {
                        return Err("postprocessing error".into());
                    }
                }
                Err(e) => {
                    if self.solver.postprocess(Err(e)).is_ok() {
                        return Ok(());
                    } else {
                        return Err("postprocessing error".into());
                    }
                }
            }
        }
    }
    fn render_frame(&self, frame: &mut Frame) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Min(5), Constraint::Min(5)])
            .split(frame.size());
        let d1: f64 = 0.1 + (self.counter as f64).log2();
        let d2: f64 = 1.0;
        let v1 = (1isize..50)
            .map(|n| {
                let x = (n as f64 / 25.0) - 1.0;
                (x, ((x * d2 + d1) * 6.0).sin())
            })
            .collect::<Vec<_>>();
        let v2 = (1isize..50)
            .map(|n| {
                let x = (n as f64 / 25.0) - 1.0;
                (x, ((x * d2 + d1) * 6.0).cos())
            })
            .collect::<Vec<_>>();
        let dataset: Vec<Dataset> = vec![
            Dataset::default()
                .name("sin() wave")
                .marker(symbols::Marker::Dot)
                .style(Style::default().fg(Color::Cyan))
                .data(&v1),
            Dataset::default()
                .name("cosine() wave")
                .marker(symbols::Marker::Dot)
                .style(Style::default().fg(Color::Red))
                .data(&v2),
        ];
        let chart = self.chart(dataset);
        let bar_chart = self.bar_chart();
        frame.render_widget(chart, chunks[0]);
        frame.render_widget(bar_chart, chunks[1]);
    }
    fn handle_events(&mut self) -> io::Result<bool> {
        if let Event::Key(key_event) = event::read()? {
            if key_event.kind == KeyEventKind::Press {
                match key_event.code {
                    KeyCode::Char('q') => return Ok(true),
                    KeyCode::Left => self.decrement_counter()?,
                    KeyCode::Right => self.increment_counter()?,
                    _ => (),
                }
            }
        }
        Ok(false)
    }
    fn decrement_counter(&mut self) -> io::Result<()> {
        if let Some(n) = self.counter.checked_sub(1) {
            self.counter = n;
        }
        Ok(())
    }
    fn increment_counter(&mut self) -> io::Result<()> {
        if let Some(n) = self.counter.checked_add(1) {
            self.counter = n;
        }
        Ok(())
    }
}

impl App {
    fn bar_chart(&self) -> BarChart<'_> {
        let b = vec![
            ("core", self.asg_stats[0]),
            ("fixed", self.asg_stats[1]),
            ("elim", self.asg_stats[2]),
            ("data4", 3),
            ("data5", 5),
            ("data6", 10),
            ("data7", 6),
            ("data8", 18),
            ("data9", 5),
        ];
        let barchart = BarChart::default()
            .block(Block::bordered().title("BarChart of `10.0 * log_2(n)`"))
            .data(&b)
            .bar_width(7)
            .bar_style(Style::default().fg(Color::Red))
            .value_style(Style::default().fg(Color::White).bg(Color::Blue));
        barchart
    }
    fn chart<'a>(&'a self, dataset: Vec<Dataset<'a>>) -> Chart<'a> {
        let x_labels = vec![
            Span::styled("-1.0", Style::default()),
            Span::styled("-0.5", Style::default()),
            Span::styled("0.0", Style::default()),
            Span::styled("0.5", Style::default()),
            Span::styled("1.0", Style::default()),
        ];
        let y_labels = vec![
            Span::styled("-2", Style::default()),
            Span::styled("-1", Style::default()),
            Span::styled("0", Style::default()),
            Span::styled("1", Style::default()),
            Span::styled("2", Style::default()),
        ];
        let chart = Chart::new(dataset)
            .block(
                Block::bordered()
                    .title(" Chart 1 ".cyan().bold())
                    .title_alignment(Alignment::Center),
            )
            .x_axis(
                Axis::default()
                    .title("X axis")
                    .style(Style::default().fg(Color::Gray))
                    .labels(x_labels)
                    .bounds([-1.0, 1.0]),
            )
            .y_axis(
                Axis::default()
                    .title("Y axis")
                    .style(Style::default().fg(Color::Gray))
                    .labels(y_labels)
                    .bounds([-2.0, 2.0]),
            );
        chart
        // chart.render(area, buf);
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut config = Config::default();
    config.inject_from_args();
    config.splr_interface = false;
    if !config.cnf_file.exists() {
        println!(
            "{} does not exist.",
            config.cnf_file.file_name().unwrap().to_str().unwrap()
        );
        return Ok(());
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
        return Ok(());
    }
    if let Ok(val) = env::var("SPLR_TIMEOUT") {
        if let Ok(splr_timeout) = val.parse::<u64>() {
            let input = cnf_file.as_ref().to_string();
            let no_color = config.no_color;
            thread::spawn(move || {
                thread::sleep(Duration::from_millis(splr_timeout * 1000));
                println!(
                    "{} (TimeOut): {}",
                    colored(Err(&SolverError::TimeOut), no_color),
                    input
                );
                std::process::exit(0);
            });
        }
    }
    let mut splr = match Splr::build(&config) {
        Err(SolverError::EmptyClause | SolverError::RootLevelConflict(_)) => {
            println!(
                "\x1B[1G\x1B[K{}: {}",
                colored(Ok(false), config.no_color),
                config.cnf_file.file_name().unwrap().to_string_lossy(),
            );
            std::process::exit(20);
        }
        Err(e) => {
            panic!("{e:?}");
        }
        Ok(solver) => solver,
    };
    let Ok(sc) = splr.prepare() else {
        return Err("failed to start SAT preproecss".into());
    };
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let mut app = App::solver(splr, sc);
    let result = app.run(&mut terminal);

    disable_raw_mode()?;
    execute!(terminal.backend_mut(), LeaveAlternateScreen)?;
    terminal.show_cursor()?;
    if let Err(err) = result {
        println!("{err:?}");
    }
    let res: Result<Certificate, SolverError> = Ok(Certificate::UNSAT);
    save_result(&mut app.solver, &res, &cnf_file, ans_file);
    Ok(())
}

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
            Ok(false) => Cow::from(format!("{BLUE}s UNSATISFIABLE{RESET}")),
            Ok(true) => Cow::from(format!("{GREEN}s SATISFIABLE{RESET}")),
            Err(_) => Cow::from(format!("{RED}s UNKNOWN{RESET}")),
        }
    }
}
fn save_result<S: AsRef<str> + std::fmt::Display>(
    s: &mut Splr,
    res: &SolverResult,
    input: S,
    output: Option<PathBuf>,
) {
    let mut ofile;
    let mut otty;
    let mut redirect = false;
    let mut buf: &mut dyn io::Write = match output {
        Some(ref file) => {
            if let Ok(f) = File::create(file) {
                ofile = io::BufWriter::new(f);
                &mut ofile
            } else {
                redirect = true;
                otty = io::BufWriter::new(std::io::stdout());
                &mut otty
            }
        }
        None => {
            otty = io::BufWriter::new(std::io::stdout());
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
                    format!("c This file was generated by splr-{VERSION} for {input}\nc \n")
                        .as_bytes(),
                )?;
                report(s, buf)?;
                buf.write_all(b"s SATISFIABLE\nv ")?;
                for x in v {
                    buf.write_all(format!("{x} ").as_bytes())?;
                }
                buf.write(b"0\n")
            })() {
                println!("Abort: failed to save by {why}!");
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
                        "c The empty assignment set generated by splr-{VERSION} for {input}\nc \n",
                    )
                    .as_bytes(),
                )?;
                report(s, &mut buf)?;
                buf.write_all(b"s UNSATISFIABLE\n")?;
                buf.write_all(b"0\n")
            })() {
                println!("Abort: failed to save by {why}!");
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
                    format!("c An assignment set generated by splr-{VERSION} for {input}\nc \n",)
                        .as_bytes(),
                )?;
                report(s, buf)?;
                buf.write_all(format!("c {}\n{}\n", e, colored(Err(e), true)).as_bytes())?;
                buf.write(b"0\n")
            })() {
                println!("Abort: failed to save by {why}!");
            }
        }
    }
}

fn report(s: &Splr, out: &mut dyn io::Write) -> std::io::Result<()> {
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
            "c  #conflict:{:>11}, #decision:{:>13}, #propagate:{:>15},\n",
            state[LogUsizeId::NumConflict],
            state[LogUsizeId::NumDecision],
            state[LogUsizeId::NumPropagate],
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c   Assignment|#rem:{:>9}, #fix:{:>9}, #elm:{:>9}, prg%:{:>9.4},\n",
            state[LogUsizeId::RemainingVar],
            state[LogUsizeId::AssertedVar],
            state[LogUsizeId::EliminatedVar],
            state[LogF64Id::Progress],
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c       Clause|Remv:{:>9}, LBD2:{:>9}, BinC:{:>9}, Perm:{:>9},\n",
            state[LogUsizeId::RemovableClause],
            state[LogUsizeId::LBD2Clause],
            state[LogUsizeId::BiClause],
            state[LogUsizeId::PermanentClause],
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c     Conflict|entg:{:>9.4}, cLvl:{:>9.4}, bLvl:{:>9.4}, /cpr:{:>9.2},\n",
            state[LogF64Id::LiteralBlockEntanglement],
            state[LogF64Id::CLevel],
            state[LogF64Id::BLevel],
            state[LogF64Id::ConflictPerRestart],
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c      Learing|avrg:{:>9.4}, trnd:{:>9.4}, #RST:{:>9}, /dpc:{:>9.2},\n",
            state[LogF64Id::EmaLBD],
            state[LogF64Id::TrendLBD],
            state[LogUsizeId::Restart],
            state[LogF64Id::DecisionPerConflict],
        )
        .as_bytes(),
    )?;
    out.write_all(
        format!(
            "c         misc|vivC:{:>9}, subC:{:>9}, core:{:>9}, /ppc:{:>9.2},\n",
            state[LogUsizeId::VivifiedClause],
            state[LogUsizeId::SubsumedClause],
            state[LogUsizeId::UnreachableCore],
            state[LogF64Id::PropagationPerConflict],
        )
        .as_bytes(),
    )?;
    out.write_all(format!("c     Strategy|mode:  generic, time:{tm:9.2},\n").as_bytes())?;
    out.write_all("c \n".as_bytes())?;
    for key in &config::property::F64S {
        out.write_all(
            format!(
                "c   config::{:<27}{:>19.3}\n",
                format!("{key:?}"),
                s.state.config.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &assign::property::USIZES {
        out.write_all(
            format!(
                "c   assign::{:<27}{:>15}\n",
                format!("{key:?}"),
                s.asg.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &assign::property::EMAS {
        out.write_all(
            format!(
                "c   assign::{:<27}{:>19.3}\n",
                format!("{key:?}"),
                s.asg.refer(*key).get(),
            )
            .as_bytes(),
        )?;
    }
    for key in &cdb::property::USIZES {
        out.write_all(
            format!(
                "c   clause::{:<27}{:>15}\n",
                format!("{key:?}"),
                s.cdb.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &cdb::property::F64 {
        out.write_all(
            format!(
                "c   clause::{:<27}{:>19.3}\n",
                format!("{key:?}"),
                s.cdb.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &state::property::USIZES {
        out.write_all(
            format!(
                "c   state::{:<28}{:>15}\n",
                format!("{key:?}"),
                s.state.derefer(*key),
            )
            .as_bytes(),
        )?;
    }
    for key in &state::property::EMAS {
        out.write_all(
            format!(
                "c   state::{:<28}{:>19.3}\n",
                format!("{key:?}"),
                s.state.refer(*key).get(),
            )
            .as_bytes(),
        )?;
    }

    out.write_all(b"c \n")?;
    Ok(())
}
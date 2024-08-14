// Splr with TUI
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
        widgets::{block::*, *},
    },
    splr::{
        assign::{self, AssignIF, VarManipulateIF},
        cdb,
        config::{self, CERTIFICATION_DEFAULT_FILENAME},
        solver::Solver as Splr,
        solver::{Certificate, SatSolverIF, SearchState, SolveIF, SolverResult},
        state::{self, LogF64Id, LogUsizeId},
        types::{FlagIF, FlagVar},
        Config, EmaIF, PropertyDereference, PropertyReference, SolverError, VERSION,
    },
    std::{
        borrow::Cow,
        collections::HashMap,
        env,
        error::Error,
        fs::File,
        io,
        path::PathBuf,
        thread,
        time::{Duration, Instant},
    },
};

mod restart {
    use {
        ratatui::{
            prelude::*,
            style::Color,
            widgets::{block::*, *},
        },
        splr::{
            assign,
            solver::{SearchState, Solver as Splr},
            EmaIF, PropertyReference,
        },
        std::collections::VecDeque,
    };

    const LEN: usize = 80;

    #[derive(Debug, Default)]
    pub(super) struct Observer {
        hist: VecDeque<(usize, f64)>,
        cpr: Vec<(f64, f64)>,
        spans: Vec<(f64, f64)>,
    }

    impl Observer {
        pub(super) fn reflect(&mut self, solver: &Splr, state: &mut SearchState) {
            let span = *state.span_history.iter().max().unwrap_or(&1);
            state.span_history.clear();
            let result = solver
                .asg
                .refer(assign::property::TEma::ConflictPerRestart)
                .get();
            self.hist.push_back((span, result));
            if LEN < self.hist.len() {
                self.hist.pop_front();
            }
        }
        pub(super) fn build_chart(&mut self) -> Chart<'_> {
            self.spans = self
                .hist
                .iter()
                .enumerate()
                .map(|(i, d)| (i as f64, (d.0 as f64).log2().clamp(2.0, 6.0)))
                .collect::<Vec<_>>();
            self.cpr = self
                .hist
                .iter()
                .enumerate()
                .map(|(i, d)| (i as f64, d.1.log2().clamp(2.0, 6.0)))
                .collect::<Vec<_>>();
            let x_labels = vec![
                Span::styled(format!("-{}", LEN), Style::default()),
                Span::styled(format!("-{}", 3 * LEN / 4), Style::default()),
                Span::styled(format!("-{}", LEN / 2), Style::default()),
                Span::styled(format!("-{}", LEN / 4), Style::default()),
                Span::styled(" 0", Style::default()),
            ];
            let y_labels = vec![
                Span::styled(" lg(4)", Style::default()),
                Span::styled(" lg(8)", Style::default()),
                Span::styled("lg(16)", Style::default()),
                Span::styled("lg(32)", Style::default()),
                Span::styled("lg(64)", Style::default()),
            ];
            let chart = Chart::new(vec![
                Dataset::default()
                    .data(&self.spans)
                    .style(Style::default().fg(Color::Black))
                    .marker(symbols::Marker::Braille),
                Dataset::default()
                    .data(&self.cpr)
                    .style(Style::default().fg(Color::LightRed))
                    .marker(symbols::Marker::Dot),
            ])
            .block(
                Block::bordered().title(
                    "Log-scaled Restart Gap (conflicts per restart)"
                        .cyan()
                        .bold(),
                ), // .title_alignment(Alignment::Center),
            )
            .x_axis(
                Axis::default()
                    .title("restart")
                    .style(Style::default().fg(Color::Gray))
                    .labels(x_labels)
                    .bounds([0.0, LEN as f64]),
            )
            .y_axis(
                Axis::default()
                    .title("gap")
                    .style(Style::default().fg(Color::Gray))
                    .labels(y_labels)
                    .bounds([0.0, 8.0]),
            );
            chart
        }
    }
}

#[cfg(feature = "spin")]
mod spin {
    use {
        ratatui::{
            prelude::*,
            style::Color,
            widgets::{block::*, *},
        },
        splr::{
            assign::{AssignIF, VarManipulateIF},
            solver::Solver as Splr,
            types::{FlagIF, FlagVar},
        },
        std::collections::HashMap,
    };

    #[derive(Debug, Default)]
    pub(super) struct Observer {
        var_spin_hist: HashMap<usize, f64>,
        spin_stats: [u64; 11],
        var_spin_shift_stats: [u64; 21],
    }
    impl Observer {
        pub fn reflect(&mut self, solver: &Splr) {
            let root_level = solver.asg.root_level();
            // build spin stats data
            let spin_distribution: Vec<f64> = {
                let mut h: [usize; 10] = [0; 10];
                let mut num_var: usize = 0;
                solver.asg.var_iter().for_each(|v| {
                    if !v.is(FlagVar::ELIMINATED) && !v.is_fixed(root_level) {
                        num_var += 1;
                        h[(v.spin_energy().0.clamp(0.0, 0.99) / 0.1) as usize] += 1;
                    }
                });
                h.iter()
                    .map(|c| (*c as f64) / (num_var as f64))
                    .collect::<Vec<f64>>()
            };
            for (i, d) in spin_distribution.iter().enumerate().take(10) {
                self.spin_stats[i] = (d * 100.0) as u64;
            }
            // make spin history histogram
            let spins: Vec<f64> = solver
                .asg
                .var_iter()
                .map(|v| v.spin_energy().0.clamp(0.0, 1.0))
                .collect::<Vec<_>>();
            let spin_transition: Vec<f64> = spins
                .iter()
                .enumerate()
                .map(|(vi, val)| {
                    (*val - *self.var_spin_hist.get(&vi).unwrap_or(&0.0)).clamp(-1.0, 1.0)
                })
                .collect::<Vec<_>>();
            spins.iter().enumerate().for_each(|(i, v)| {
                self.var_spin_hist.insert(i, *v);
            });
            let spin_histogram: Vec<f64> = {
                let mut h: [usize; 21] = [0; 21];
                let mut num_var: usize = 0;
                solver.asg.var_iter().enumerate().for_each(|(va, v)| {
                    if 0 < va && !v.is(FlagVar::ELIMINATED) && !v.is_fixed(root_level) {
                        num_var += 1;
                        h[((1.0 + spin_transition[va]) / 0.1) as usize] += 1;
                    }
                });
                h.iter()
                    .map(|c| (*c as f64) / (num_var as f64))
                    .collect::<Vec<f64>>()
            };
            for (i, d) in spin_histogram.iter().enumerate().take(21) {
                self.var_spin_shift_stats[i] = (d * 100.0) as u64;
            }
        }
        pub fn build_bar_chart1(&self) -> BarChart<'_> {
            let b = vec![
                ("0.0", self.spin_stats[0]),
                ("0.1", self.spin_stats[1]),
                ("0.2", self.spin_stats[2]),
                ("0.3", self.spin_stats[3]),
                ("0.4", self.spin_stats[4]),
                ("0.5", self.spin_stats[5]),
                ("0.6", self.spin_stats[6]),
                ("0.7", self.spin_stats[7]),
                ("0.8", self.spin_stats[8]),
                ("0.9", self.spin_stats[9]),
                ("1.0", self.spin_stats[10]),
            ];
            let barchart = BarChart::default()
                .block(Block::bordered().title("Var Spin Energy Histogram"))
                .data(&b)
                .bar_width(7)
                .bar_style(Style::default().fg(Color::Red))
                .value_style(Style::default().fg(Color::White).bg(Color::Blue));
            barchart
        }
        pub fn build_bar_chart2(&self) -> BarChart<'_> {
            let b = vec![
                ("-1.", self.var_spin_shift_stats[0]),
                ("-.9", self.var_spin_shift_stats[1]),
                ("-.8", self.var_spin_shift_stats[2]),
                ("-.7", self.var_spin_shift_stats[3]),
                ("-.6", self.var_spin_shift_stats[4]),
                ("-.5", self.var_spin_shift_stats[5]),
                ("-.4", self.var_spin_shift_stats[6]),
                ("-.3", self.var_spin_shift_stats[7]),
                ("-.2", self.var_spin_shift_stats[8]),
                ("-.1", self.var_spin_shift_stats[9]),
                ("0.0", self.var_spin_shift_stats[10]),
                ("0.1", self.var_spin_shift_stats[11]),
                ("0.2", self.var_spin_shift_stats[12]),
                ("0.3", self.var_spin_shift_stats[13]),
                ("0.4", self.var_spin_shift_stats[14]),
                ("0.5", self.var_spin_shift_stats[15]),
                ("0.6", self.var_spin_shift_stats[16]),
                ("0.7", self.var_spin_shift_stats[17]),
                ("0.8", self.var_spin_shift_stats[18]),
                ("0.9", self.var_spin_shift_stats[19]),
                ("1.0", self.var_spin_shift_stats[20]),
            ];
            let barchart = BarChart::default()
                .block(Block::bordered().title("Var Spin Transition Histogram"))
                .data(&b)
                .bar_width(3)
                .bar_style(Style::default().fg(Color::Red))
                .value_style(Style::default().fg(Color::White).bg(Color::Blue));
            barchart
        }
    }
}

#[derive(Debug)]
pub struct App {
    solver: Splr,
    state: SearchState,
    counter: i16,
    restart_view: restart::Observer,

    #[cfg(feature = "spin")]
    spin_view: spin::Observer,

    var_act_hist: HashMap<usize, f64>,
    act_stats: [u64; 11],
    var_act_shift_stats: [u64; 21],
}

impl App {
    fn solver(solver: Splr, state: SearchState) -> Self {
        App {
            solver,
            state,
            counter: 0,
            act_stats: [0; 11],
            var_act_shift_stats: [0; 21],
            var_act_hist: HashMap::new(),
            restart_view: restart::Observer::default(),

            #[cfg(feature = "spin")]
            spin_view: spin::Observer::default(),
        }
    }
    fn run<B: Backend>(&mut self, terminal: &mut Terminal<B>) -> Result<(), Box<dyn Error>> {
        macro_rules! _scaling {
            ($n: expr) => {
                (($n.max(1) as f64).log2() * 10.0) as u64
            };
        }
        let timeout = Duration::from_millis(0);
        let root_level = self.solver.asg.root_level();
        loop {
            // call solver
            self.counter += 1;
            let ret: Result<Option<bool>, SolverError> = {
                let App {
                    ref mut solver,
                    state: ref mut ss,
                    ..
                } = self;
                solver.search_stage(ss)
            };
            // build stats data
            let activity_distribution: Vec<f64> = {
                let mut h: [usize; 11] = [0; 11];
                let mut num_var: usize = 0;
                self.solver.asg.var_iter().for_each(|v| {
                    if !v.is(FlagVar::ELIMINATED) && !v.is_fixed(root_level) {
                        num_var += 1;
                        h[(v.activity() / 0.1) as usize] += 1;
                    }
                });
                h.iter()
                    .map(|c| (*c as f64) / (num_var as f64))
                    .collect::<Vec<f64>>()
            };
            for (i, d) in activity_distribution.iter().enumerate().take(10) {
                self.act_stats[i] = (d * 100.0) as u64;
            }
            // make history histogram
            let va: Vec<f64> = self
                .solver
                .asg
                .var_iter()
                .map(|v| v.activity())
                .collect::<Vec<_>>();
            let activity_transition: Vec<f64> = va
                .iter()
                .enumerate()
                .map(|(vi, val)| {
                    (*val - *self.var_act_hist.get(&vi).unwrap_or(&0.0)).clamp(-1.0, 1.0)
                })
                .collect::<Vec<_>>();
            va.iter().enumerate().for_each(|(i, v)| {
                self.var_act_hist.insert(i, *v);
            });
            let activity_histogram: Vec<f64> = {
                let mut h: [usize; 21] = [0; 21];
                let mut num_var: usize = 0;
                self.solver.asg.var_iter().enumerate().for_each(|(va, v)| {
                    if 0 < va && !v.is(FlagVar::ELIMINATED) && !v.is_fixed(root_level) {
                        num_var += 1;
                        h[((1.0 + activity_transition[va]) / 0.1) as usize] += 1;
                    }
                });
                h.iter()
                    .map(|c| (*c as f64) / (num_var as f64))
                    .collect::<Vec<f64>>()
            };
            for (i, d) in activity_histogram.iter().enumerate().take(21) {
                self.var_act_shift_stats[i] = (d * 100.0) as u64;
            }

            self.restart_view.reflect(&self.solver, &mut self.state);
            #[cfg(feature = "spin")]
            self.spin_view.reflect(&self.solver);

            // draw them
            terminal.draw(|f| self.render_frame(f))?;
            // check termination conditions
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
    fn render_frame(&mut self, frame: &mut Frame) {
        let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints(
                #[cfg(feature = "spin")]
                [
                    Constraint::Min(5),
                    Constraint::Min(5),
                    Constraint::Min(5),
                    Constraint::Min(5),
                    Constraint::Min(5),
                ],
                #[cfg(not(feature = "spin"))]
                [Constraint::Min(5), Constraint::Min(5), Constraint::Min(5)],
            )
            .split(frame.area());
        frame.render_widget(self.var_activity_bar_chart(), chunks[0]);
        frame.render_widget(self.va_history_bar_chart(), chunks[1]);
        frame.render_widget(self.restart_view.build_chart(), chunks[2]);
        #[cfg(feature = "spin")]
        {
            frame.render_widget(self.spin_view.build_bar_chart1(), chunks[3]);
            frame.render_widget(self.spin_view.build_bar_chart2(), chunks[4]);
        }
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
    /// var activity histogram
    fn var_activity_bar_chart(&self) -> BarChart<'_> {
        let b = vec![
            ("0.0", self.act_stats[0]),
            ("0.1", self.act_stats[1]),
            ("0.2", self.act_stats[2]),
            ("0.3", self.act_stats[3]),
            ("0.4", self.act_stats[4]),
            ("0.5", self.act_stats[5]),
            ("0.6", self.act_stats[6]),
            ("0.7", self.act_stats[7]),
            ("0.8", self.act_stats[8]),
            ("0.9", self.act_stats[9]),
            ("1.0", self.act_stats[10]),
        ];
        let barchart = BarChart::default()
            .block(Block::bordered().title("Var Activity Histogram"))
            .data(&b)
            .bar_width(7)
            .bar_style(Style::default().fg(Color::Red))
            .value_style(Style::default().fg(Color::White).bg(Color::Blue));
        barchart
    }
    fn va_history_bar_chart(&self) -> BarChart<'_> {
        let b = vec![
            ("-1.", self.var_act_shift_stats[0]),
            ("-.9", self.var_act_shift_stats[1]),
            ("-.8", self.var_act_shift_stats[2]),
            ("-.7", self.var_act_shift_stats[3]),
            ("-.6", self.var_act_shift_stats[4]),
            ("-.5", self.var_act_shift_stats[5]),
            ("-.4", self.var_act_shift_stats[6]),
            ("-.3", self.var_act_shift_stats[7]),
            ("-.2", self.var_act_shift_stats[8]),
            ("-.1", self.var_act_shift_stats[9]),
            ("0.0", self.var_act_shift_stats[10]),
            ("0.1", self.var_act_shift_stats[11]),
            ("0.2", self.var_act_shift_stats[12]),
            ("0.3", self.var_act_shift_stats[13]),
            ("0.4", self.var_act_shift_stats[14]),
            ("0.5", self.var_act_shift_stats[15]),
            ("0.6", self.var_act_shift_stats[16]),
            ("0.7", self.var_act_shift_stats[17]),
            ("0.8", self.var_act_shift_stats[18]),
            ("0.9", self.var_act_shift_stats[19]),
            ("1.0", self.var_act_shift_stats[20]),
        ];
        let barchart = BarChart::default()
            .block(Block::bordered().title("Var Activity Moving History"))
            .data(&b)
            .bar_width(3)
            .bar_style(Style::default().fg(Color::Red))
            .value_style(Style::default().fg(Color::White).bg(Color::Blue));
        barchart
    }
    fn _chart<'a>(&'a self, dataset: Vec<Dataset<'a>>) -> Chart<'a> {
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
    let Ok(ss) = splr.prepare() else {
        return Err("failed to start SAT preproecss".into());
    };
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let mut app = App::solver(splr, ss);
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

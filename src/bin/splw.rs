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
    std::{
        error::Error,
        io,
        time::{Duration, Instant},
    },
};

#[derive(Debug)]
pub struct App {
    counter: i16,
    #[allow(dead_code)]
    start: Instant,
}
impl Default for App {
    fn default() -> Self {
        App {
            counter: 0,
            start: Instant::now(),
        }
    }
}

impl App {
    fn run<B: Backend>(&mut self, terminal: &mut Terminal<B>) -> io::Result<()> {
        let timeout = Duration::from_millis(0);
        loop {
            terminal.draw(|f| self.render_frame(f))?;
            if crossterm::event::poll(timeout)? {
                if self.handle_events()? {
                    return Ok(());
                };
                // self.on_tick();
            }
            self.counter += 1;
            /* if tick_rate < self.start.elapsed() {
                self.start = Instant::now();
            } */
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
    fn bar_chart<'a>(&'a self) -> BarChart<'a> {
        let b = vec![
            ("data0", 2),
            ("data1", 4),
            ("data2", 1),
            ("data3", (self.counter.max(1) as f64).log2() as u64),
            ("data4", 3),
            ("data5", 5),
            ("data6", 10),
            ("data7", 6),
            ("data8", 18),
            ("data9", 5),
        ];
        let barchart = BarChart::default()
            .block(Block::bordered().title("BarChart"))
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
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let res = App::default().run(&mut terminal);

    disable_raw_mode()?;
    execute!(terminal.backend_mut(), LeaveAlternateScreen)?;
    terminal.show_cursor()?;
    if let Err(err) = res {
        println!("{err:?}");
    }
    Ok(())
}

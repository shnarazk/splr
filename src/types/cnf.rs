use {
    super::SolverError,
    std::{
        fmt,
        fs::File,
        io::{BufRead, BufReader},
        path::Path,
    },
};

/// CNF locator
#[derive(Clone, Debug, Default)]
pub enum CNFIndicator {
    /// not specified
    #[default]
    Void,
    /// from a file
    File(String),
    /// embedded directly
    LitVec(usize),
}

impl fmt::Display for CNFIndicator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CNFIndicator::Void => write!(f, "No CNF specified)"),
            CNFIndicator::File(file) => write!(f, "CNF file({file})"),
            CNFIndicator::LitVec(n) => write!(f, "A vec({n} clauses)"),
        }
    }
}

// impl CNFIndicator {
//     pub fn to_string(&self) -> String {
//         match self {
//             CNFIndicator::Void => "(no cnf)".to_string(),
//             CNFIndicator::File(f) => f.to_string(),
//             CNFIndicator::LitVec(v) => format!("(embedded {} element vector)", v.len()).to_string(),
//         }
//     }
// }

/// Data storage about a problem.
#[derive(Clone, Debug)]
pub struct CNFDescription {
    pub num_of_variables: usize,
    pub num_of_clauses: usize,
    pub pathname: CNFIndicator,
}

impl Default for CNFDescription {
    fn default() -> CNFDescription {
        CNFDescription {
            num_of_variables: 0,
            num_of_clauses: 0,
            pathname: CNFIndicator::Void,
        }
    }
}

impl fmt::Display for CNFDescription {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let CNFDescription {
            num_of_variables: nv,
            num_of_clauses: nc,
            pathname: path,
        } = &self;
        write!(f, "CNF({nv}, {nc}, {path})")
    }
}

impl<V: AsRef<[i32]>> From<&[V]> for CNFDescription {
    fn from(vec: &[V]) -> Self {
        let num_of_variables = vec
            .iter()
            .map(|clause| clause.as_ref().iter().map(|l| l.abs()).max().unwrap_or(0))
            .max()
            .unwrap_or(0) as usize;
        CNFDescription {
            num_of_variables,
            num_of_clauses: vec.len(),
            pathname: CNFIndicator::LitVec(vec.len()),
        }
    }
}

/// A wrapper structure to make a CNFDescription from a file.
/// To make CNFDescription clone-able, a BufReader should be separated from it.
/// If you want to make a CNFDescription which isn't connected to a file,
/// just call CNFDescription::default() directly.
#[derive(Debug)]
pub struct CNFReader {
    pub cnf: CNFDescription,
    pub reader: BufReader<File>,
}

impl TryFrom<&Path> for CNFReader {
    type Error = SolverError;
    fn try_from(path: &Path) -> Result<Self, Self::Error> {
        let pathname = if path.to_string_lossy().is_empty() {
            "--".to_string()
        } else {
            Path::new(&path.to_string_lossy().into_owned())
                .file_name()
                .map_or("aStrangeNamed".to_string(), |f| {
                    f.to_string_lossy().into_owned()
                })
        };
        let fs = File::open(path).map_or(Err(SolverError::IOError), Ok)?;
        let mut reader = BufReader::new(fs);
        let mut buf = String::new();
        let mut nv: usize = 0;
        let mut nc: usize = 0;
        let mut found_valid_header = false;
        loop {
            buf.clear();
            match reader.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_k) => {
                    let mut iter = buf.split_whitespace();
                    if iter.next() == Some("p") && iter.next() == Some("cnf") {
                        if let Some(v) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                            if let Some(c) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                                nv = v;
                                nc = c;
                                found_valid_header = true;
                                break;
                            }
                        }
                    }
                    continue;
                }
                Err(e) => {
                    println!("{e}");
                    return Err(SolverError::IOError);
                }
            }
        }
        if !found_valid_header {
            return Err(SolverError::IOError);
        }
        let cnf = CNFDescription {
            num_of_variables: nv,
            num_of_clauses: nc,
            pathname: CNFIndicator::File(pathname),
        };
        Ok(CNFReader { cnf, reader })
    }
}

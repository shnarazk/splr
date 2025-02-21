// pub mod cnf;
// pub use self::cnf::*;
use {
    rustc_data_structures::fx::FxHashSet,
    std::{
        fs::File,
        io::{BufRead, BufReader},
        path::Path,
    },
};

const TOO_MANY_CLAUSES: usize = 100_000;

pub type Clause = Vec<i32>;

#[derive(Debug, Eq, PartialEq)]
pub enum CNFOperationError {
    AddingClauseExists,
    AddingEmptyClause,
    AddignConflictingAssingment,
    ReadingCNFFile,
    ParsingCNF,
    CreatingCNFFile,
    WritingCNFFile,
    UnknownError(String),
}

#[derive(Debug, Default, Eq, PartialEq)]
pub struct CNF {
    num_vars: u32,
    assign: FxHashSet<i32>,
    clauses: Vec<Clause>,
    cls_map: FxHashSet<Vec<i32>>,
    no_check_uniqueness: bool,
}

impl std::fmt::Display for CNF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "CNF({} vars, {} clauses)",
            self.num_vars(),
            self.num_clauses()
        )
    }
}

pub trait CnfIF: Sized {
    type Error;
    // Add a `Clause` and returns:
    // - `Some(self)`: if add it successfully
    // - `None`: if the clause is in it already
    fn add_clause<C: AsRef<Clause>>(&mut self, clause: C) -> Result<&mut CNF, Self::Error>;
    fn from_vec_i32<V: AsRef<[Clause]>>(clauses: V) -> Result<Self, Self::Error>;
    fn load(file: &Path) -> Result<Self, Self::Error>;
    fn num_vars(&self) -> u32;
    fn num_clauses(&self) -> usize;
    fn save(&self, file: &Path) -> Result<(), Self::Error>;
    fn dump_to_string(&self) -> String;
}

impl CnfIF for CNF {
    type Error = CNFOperationError;
    fn add_clause<C: AsRef<Clause>>(&mut self, clause: C) -> Result<&mut CNF, Self::Error> {
        let c = clause.as_ref().clone();
        let mut cc = c.clone();
        cc.sort_unstable();
        if !self.no_check_uniqueness && TOO_MANY_CLAUSES < self.clauses.len() {
            self.no_check_uniqueness = true;
            self.cls_map.clear();
        }
        if !self.no_check_uniqueness && self.cls_map.iter().any(|ref_c| *ref_c == cc) {
            return Err(CNFOperationError::AddingClauseExists);
        }
        // assert!(!c.is_empty());
        if c.is_empty() {
            return Err(CNFOperationError::AddingEmptyClause);
        }
        self.num_vars = self
            .num_vars
            .max(c.iter().map(|v| v.unsigned_abs()).max().unwrap());
        if !self.no_check_uniqueness {
            self.cls_map.insert(cc);
        }
        self.clauses.push(c);
        Ok(self)
    }
    fn from_vec_i32<V: AsRef<[Clause]>>(clauses: V) -> Result<Self, Self::Error> {
        let mut cnf: CNF = CNF::default();
        let mut max_var: u32 = 0;
        for ref_c in clauses.as_ref().iter() {
            match ref_c.len() {
                0 => {
                    return Err(CNFOperationError::AddingEmptyClause);
                }
                1 => {
                    let l: i32 = ref_c[0];
                    if cnf.assign.contains(&-l) {
                        return Err(CNFOperationError::AddignConflictingAssingment);
                    }
                    cnf.assign.insert(l);
                }
                _ => {
                    let mut cc = ref_c.clone();
                    cc.sort_unstable();
                    cnf.cls_map.insert(cc);
                    cnf.clauses.push(ref_c.clone());
                }
            }
            max_var = max_var.max(ref_c.iter().map(|v| v.unsigned_abs()).max().unwrap());
        }
        cnf.num_vars = max_var;
        Ok(cnf)
    }
    fn load(path: &Path) -> Result<Self, Self::Error> {
        let fs = File::open(path).map_err(|_| CNFOperationError::ReadingCNFFile)?;
        let mut reader = BufReader::new(fs);
        let mut buf = String::new();
        let mut nv: u32 = 0;
        let mut nc: usize = 0;
        let mut num_clause: usize = 0;
        let mut found_valid_header = false;
        let mut clause_extists_already = false;
        let mut cnf = CNF::default();
        loop {
            buf.clear();
            match reader.read_line(&mut buf) {
                Ok(0) => break,
                Ok(_) if buf == "\n" => (),
                Ok(_) if buf.starts_with('c') => (),
                Ok(_) if found_valid_header => {
                    let mut vec: Vec<i32> = Vec::new();
                    for seg in buf.split(' ') {
                        if let Ok(l) = seg.parse::<i32>() {
                            if l == 0 {
                                break;
                            }
                            vec.push(l);
                        }
                    }
                    debug_assert!(!vec.is_empty());
                    if let Err(e) = cnf.add_clause(vec) {
                        if e == CNFOperationError::AddingClauseExists {
                            clause_extists_already = true;
                        } else {
                            return Err(e);
                        }
                    } else {
                        num_clause += 1;
                    }
                }
                Ok(_) => {
                    let mut iter = buf.split_whitespace();
                    if iter.next() == Some("p") && iter.next() == Some("cnf") {
                        if let Some(v) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                            if let Some(c) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                                nv = v as u32;
                                nc = c;
                                found_valid_header = true;
                                cnf.no_check_uniqueness = TOO_MANY_CLAUSES < nc;
                            }
                        }
                    }
                }
                Err(e) => {
                    return Err(CNFOperationError::UnknownError(format!("IOError ({e:?})")));
                }
            }
        }
        if !found_valid_header {
            return Err(CNFOperationError::ParsingCNF);
        }
        if cnf.num_vars() != nv {
            println!("Warning: there are less variables than its declaration.");
        }
        if clause_extists_already {
            assert_eq!(cnf.num_clauses(), num_clause);
            println!("Warning: there are less clauses than its declaration.");
        } else if cnf.num_clauses() < TOO_MANY_CLAUSES {
            assert_eq!(cnf.num_clauses(), nc);
        }
        Ok(cnf)
    }
    fn num_vars(&self) -> u32 {
        self.num_vars
    }
    fn num_clauses(&self) -> usize {
        self.clauses.len()
    }
    fn save(&self, file: &Path) -> Result<(), Self::Error> {
        use std::io::Write;
        if let Ok(f) = File::create(file) {
            let mut buf = std::io::BufWriter::new(f);
            buf.write_all(self.dump_to_string().as_bytes())
                .map_err(|_| CNFOperationError::WritingCNFFile)
        } else {
            Err(CNFOperationError::CreatingCNFFile)
        }
    }
    fn dump_to_string(&self) -> String {
        format!(
            "p cnf {} {}\n{} 0\n",
            self.num_vars,
            self.clauses.len(),
            self.clauses
                .iter()
                .map(|cls| cls
                    .iter()
                    .map(|ch| format!("{ch}"))
                    .collect::<Vec<_>>()
                    .join(" "))
                .collect::<Vec<_>>()
                .join(" 0\n"),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn it_works() {
        let build = CNF::from_vec_i32(vec![]);
        assert!(build.is_ok());
        let mut cnf = build.unwrap();
        assert!(cnf.add_clause(vec![1, 3, 2]).is_ok());
        assert_eq!(cnf.num_clauses(), 1);
        assert_eq!(cnf.num_vars(), 3);
        assert!(cnf.add_clause(vec![-1, -4, 3]).is_ok());
        assert_eq!(cnf.num_clauses(), 2);
        assert_eq!(cnf.num_vars(), 4);
        let output = cnf.dump_to_string();
        let mut line = output.lines();
        assert_eq!(line.next(), Some("p cnf 4 2"));
        assert_eq!(line.next(), Some("1 3 2 0"));
        assert_eq!(line.next(), Some("-1 -4 3 0"));
    }
    #[test]
    fn test_load_uf8() {
        let build = CNF::load(Path::new("cnfs/uf8.cnf"));
        dbg!(build.is_ok());
        let cnf = build.unwrap();
        assert_eq!(cnf.num_clauses(), 13);
        assert_eq!(cnf.num_vars(), 8);
    }
    #[test]
    fn test_load_sample() {
        let build = CNF::load(Path::new("cnfs/sample.cnf"));
        dbg!(build.is_ok());
        let cnf = build.unwrap();
        assert_eq!(cnf.num_clauses(), 1065);
        assert_eq!(cnf.num_vars(), 250);
    }
}

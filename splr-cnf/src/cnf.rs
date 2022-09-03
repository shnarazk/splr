use std::{
    collections::HashSet,
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

pub type Clause = Vec<i32>;

#[derive(Default, Eq, PartialEq)]
pub struct CNF {
    num_vars: u32,
    assign: HashSet<i32>,
    clauses: Vec<Clause>,
    cls_map: HashSet<Vec<i32>>,
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

pub trait CnfIf: Sized {
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

impl CnfIf for CNF {
    type Error = String;
    fn add_clause<C: AsRef<Clause>>(&mut self, clause: C) -> Result<&mut CNF, Self::Error> {
        let c = clause.as_ref().clone();
        let mut cc = c.clone();
        cc.sort_unstable();
        if self.cls_map.iter().any(|ref_c| *ref_c == cc) {
            return Err("".to_string());
        }
        self.num_vars = self
            .num_vars
            .max(c.iter().map(|v| v.unsigned_abs()).max().unwrap());
        self.cls_map.insert(cc);
        self.clauses.push(c);
        Ok(self)
    }
    fn from_vec_i32<V: AsRef<[Clause]>>(clauses: V) -> Result<Self, Self::Error> {
        let mut cnf: CNF = CNF::default();
        let mut max_var: u32 = 0;
        for ref_c in clauses.as_ref().iter() {
            match ref_c.len() {
                0 => {
                    return Err("".to_string());
                }
                1 => {
                    let l: i32 = ref_c[0];
                    if cnf.assign.contains(&-l) {
                        return Err("".to_string());
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
        let fs = File::open(path).map_or(Err("SolverError::IOError".to_string()), Ok)?;
        let mut reader = BufReader::new(fs);
        let mut buf = String::new();
        let mut nv: u32 = 0;
        let mut nc: usize = 0;
        let mut found_valid_header = false;
        let mut cnf = CNF::default();
        loop {
            buf.clear();
            match reader.read_line(&mut buf) {
                Ok(0) => break,
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
                    cnf.add_clause(vec)?;
                }
                Ok(_) => {
                    let mut iter = buf.split_whitespace();
                    if iter.next() == Some("p") && iter.next() == Some("cnf") {
                        if let Some(v) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                            if let Some(c) = iter.next().map(|s| s.parse::<usize>().ok().unwrap()) {
                                nv = v as u32;
                                nc = c;
                                found_valid_header = true;
                            }
                        }
                    }
                }
                Err(e) => {
                    println!("{}", e);
                    return Err("SolverError::IOError".to_string());
                }
            }
        }
        if !found_valid_header {
            return Err("SolverError::Wrong format".to_string());
        }
        assert_eq!(nv, cnf.num_vars());
        assert_eq!(nc, cnf.num_clauses());
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
                .map_err(|_| "fail to write".to_string())
        } else {
            Err("Cant create a file".to_string())
        }
    }
    fn dump_to_string(&self) -> String {
        format!(
            "p cnf {} {}\n{}",
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
                .join("\n"),
        )
    }
}

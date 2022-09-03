use std::collections::HashSet;

pub type Clause = Vec<i32>;

#[derive(Debug, Default, Eq, PartialEq)]
pub struct CNF {
    num_vars: u32,
    assign: HashSet<i32>,
    clauses: Vec<Clause>,
    cls_map: HashSet<Vec<i32>>,
}

pub trait CnfIf: Sized {
    type Error;
    // Add a `Clause` and returns:
    // - `Some(self)`: if add it successfully
    // - `None`: if the clause is in it already
    fn add_clause<C: AsRef<Clause>>(&mut self, clause: C) -> Result<&mut CNF, Self::Error>;
    fn from_vec_i32<V: AsRef<[Clause]>>(clauses: V) -> Result<Self, Self::Error>;
    fn num_vars(&self) -> u32;
    fn num_clauses(&self) -> usize;
    fn to_string(&self) -> String;
}

impl CnfIf for CNF {
    type Error = ();
    fn add_clause<C: AsRef<Clause>>(&mut self, clause: C) -> Result<&mut CNF, Self::Error> {
        let c = clause.as_ref().clone();
        let mut cc = c.clone();
        cc.sort_unstable();
        if self.cls_map.iter().any(|ref_c| *ref_c == cc) {
            return Err(());
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
                    return Err(());
                }
                1 => {
                    let l: i32 = ref_c[0];
                    if cnf.assign.contains(&-l) {
                        return Err(());
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
    fn num_vars(&self) -> u32 {
        self.num_vars
    }
    fn num_clauses(&self) -> usize {
        self.clauses.len()
    }
    fn to_string(&self) -> String {
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

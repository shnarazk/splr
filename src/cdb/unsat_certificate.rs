use crate::types::*;
#[cfg(not(feature = "no_IO"))]
use std::{
    fs::File,
    io::{BufWriter, Write},
    path::PathBuf,
};

#[cfg(feature = "no_IO")]
#[derive(Debug, Default)]
pub struct CertificationStore();

#[cfg(feature = "no_IO")]
impl Instantiate for CertificationStore {
    fn instantiate(_config: &Config, _cnf: &CNFDescription) -> Self {
        CertificationStore()
    }
}

#[cfg(feature = "no_IO")]
impl CertificationStore {
    pub fn is_active(&self) -> bool {
        false
    }
    pub fn add_input_clause(&mut self) -> u64 {
        0
    }
    pub fn add_clause_lrat(&mut self, _clause: &[Lit], _hints: &[u64]) -> u64 {
        0
    }
    pub fn delete_clause_lrat(&mut self, _id: u64) {}
    pub fn close(&mut self) {}
}

#[cfg(not(feature = "no_IO"))]
/// Struct for LRAT UNSAT certification
#[derive(Debug, Default)]
pub struct CertificationStore {
    target: Option<PathBuf>,
    buffer: Option<BufWriter<File>>,
    /// Next sequential LRAT step ID (starts at 1)
    next_step_id: u64,
}

impl Clone for CertificationStore {
    fn clone(&self) -> Self {
        Self::default()
    }
}

#[cfg(not(feature = "no_IO"))]
impl Instantiate for CertificationStore {
    fn instantiate(config: &Config, _cnf: &CNFDescription) -> Self {
        if config.use_certification {
            let cert: PathBuf = config.io_odir.join(&config.io_pfile);
            if let Ok(out) = File::create(&cert) {
                return CertificationStore {
                    next_step_id: 1,
                    buffer: Some(BufWriter::new(out)),
                    target: Some(cert),
                };
            }
        }
        CertificationStore::default()
    }
}

#[cfg(not(feature = "no_IO"))]
impl CertificationStore {
    pub fn is_active(&self) -> bool {
        self.buffer.is_some()
    }
    /// Allocate an LRAT step ID for an original (input) clause.
    /// The clause is NOT written to the proof; the LRAT verifier knows
    /// it from the CNF file. Returns the allocated ID.
    pub fn add_input_clause(&mut self) -> u64 {
        let id = self.next_step_id;
        self.next_step_id += 1;
        id
    }
    /// Add a clause to the LRAT proof with the given propagation hints.
    /// Returns the assigned LRAT step ID.
    /// Format: `id lit1 lit2 ... litn 0 hint1 hint2 ... hintk 0\n`
    pub fn add_clause_lrat(&mut self, clause: &[Lit], hints: &[u64]) -> u64 {
        let id = self.next_step_id;
        self.next_step_id += 1;
        if let Some(ref mut buf) = self.buffer {
            if write!(buf, "{id}").is_err() {
                self.buffer = None;
                return id;
            }
            for l in clause.iter() {
                if write!(buf, " {}", i32::from(*l)).is_err() {
                    self.buffer = None;
                    return id;
                }
            }
            if buf.write_all(b" 0").is_err() {
                self.buffer = None;
                return id;
            }
            for h in hints.iter() {
                if write!(buf, " {h}").is_err() {
                    self.buffer = None;
                    return id;
                }
            }
            if buf.write_all(b" 0\n").is_err() {
                self.buffer = None;
            }
        }
        id
    }
    /// Delete a clause from the LRAT proof by its step ID.
    /// Format: `step_id d clause_id 0\n`
    pub fn delete_clause_lrat(&mut self, lrat_id: u64) {
        if lrat_id == 0 {
            return;
        }
        let step_id = self.next_step_id;
        self.next_step_id += 1;
        if let Some(ref mut buf) = self.buffer {
            if writeln!(buf, "{step_id} d {lrat_id} 0").is_err() {
                self.buffer = None;
            }
        }
    }
    pub fn close(&mut self) {
        if let Some(ref mut buf) = self.buffer {
            let _ = buf.flush();
        }
        self.buffer = None;
        self.target = None;
    }
}

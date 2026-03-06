use crate::types::*;
#[cfg(not(feature = "no_IO"))]
use std::{
    fs::File,
    io::{BufWriter, Write},
    ops::Neg,
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
    pub fn add_clause(&mut self, _clause: &[Lit]) {}
    pub fn add_clause_pr(&mut self, _clause: &[Lit], _witness: &[Lit]) {}
    pub fn delete_clause(&mut self, _vec: &[Lit]) {}
    pub fn close(&mut self) {}
}

#[cfg(not(feature = "no_IO"))]
const DUMP_INTERVAL: usize = 4096 * 16;

#[cfg(not(feature = "no_IO"))]
/// Struct for saving UNSAT certification
#[derive(Debug, Default)]
pub struct CertificationStore {
    /// clause history to make certification
    queue: Vec<i32>,
    target: Option<PathBuf>,
    buffer: Option<BufWriter<File>>,
}

impl Clone for CertificationStore {
    fn clone(&self) -> Self {
        Self::default()
    }
}

#[cfg(not(feature = "no_IO"))]
impl Instantiate for CertificationStore {
    fn instantiate(config: &Config, _cnf: &CNFDescription) -> Self {
        #[cfg(not(feature = "no_IO"))]
        if config.use_certification {
            let cert: PathBuf = config.io_odir.join(&config.io_pfile);
            if let Ok(out) = File::create(&cert) {
                return CertificationStore {
                    queue: Vec::with_capacity(DUMP_INTERVAL + 1024),
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
    pub fn add_clause(&mut self, clause: &[Lit]) {
        self.queue.push(clause.len() as i32);
        for l in clause.iter() {
            self.queue.push(i32::from(*l));
        }
        if DUMP_INTERVAL < self.queue.len() {
            self.dump_to_file();
        }
    }
    /// Add a PR (Propagation Redundancy) clause with a witness to the proof.
    /// Writes the DPR line: `l1 l2 ... lk 0 w1 w2 ... wm 0\n`
    pub fn add_clause_pr(&mut self, clause: &[Lit], witness: &[Lit]) {
        self.dump_to_file();
        if let Some(ref mut buf) = self.buffer {
            for l in clause.iter() {
                if buf
                    .write_all(format!("{} ", i32::from(*l)).as_bytes())
                    .is_err()
                {
                    self.buffer = None;
                    return;
                }
            }
            if buf.write_all(b"0 ").is_err() {
                self.buffer = None;
                return;
            }
            for l in witness.iter() {
                if buf
                    .write_all(format!("{} ", i32::from(*l)).as_bytes())
                    .is_err()
                {
                    self.buffer = None;
                    return;
                }
            }
            if buf.write_all(b"0\n").is_err() {
                self.buffer = None;
            }
        }
    }
    pub fn delete_clause(&mut self, clause: &[Lit]) {
        self.queue.push((clause.len() as i32).neg());
        for l in clause.iter() {
            self.queue.push(i32::from(*l));
        }
        if DUMP_INTERVAL < self.queue.len() {
            self.dump_to_file();
        }
    }
    pub fn close(&mut self) {
        if self.buffer.is_none() {
            return;
        }
        self.dump_to_file();
        if let Some(ref mut buf) = self.buffer {
            let _ = buf.write_all(b"0\n");
            self.buffer = None;
            self.target = None;
        }
    }
}

#[cfg(not(feature = "no_IO"))]
impl CertificationStore {
    fn dump_to_file(&mut self) {
        let mut index = 0;
        if let Some(ref mut buf) = self.buffer {
            while index < self.queue.len() {
                let l = self.queue[index];
                if l < 0 && buf.write_all(b"d ").is_err() {
                    self.buffer = None;
                    break;
                }
                for _ in 0..(l.unsigned_abs() as usize) {
                    index += 1;
                    if buf
                        .write_all(format!("{} ", self.queue[index]).as_bytes())
                        .is_err()
                    {
                        self.buffer = None;
                        return;
                    }
                }
                if buf.write_all(b"0\n").is_err() {
                    self.buffer = None;
                    break;
                }
                index += 1;
            }
        }
        self.queue.clear();
    }
}

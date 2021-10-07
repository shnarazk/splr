#[cfg(not(feature = "no_IO"))]
use {
    crate::types::*,
    std::{
        fs::File,
        io::{BufWriter, Write},
        ops::Neg,
        path::PathBuf,
    },
};

const DUMP_INTERVAL: usize = 4096 * 16;

#[derive(Debug)]
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

impl Default for CertificationStore {
    fn default() -> Self {
        CertificationStore {
            queue: Vec::new(),
            buffer: None,
            target: None,
        }
    }
}

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

impl CertificationStore {
    pub fn is_active(&self) -> bool {
        self.buffer.is_some()
    }
    #[cfg(feature = "no_IO")]
    pub fn add_clause(&mut self, _clause: &[Lit]) {}
    #[cfg(not(feature = "no_IO"))]
    pub fn add_clause(&mut self, clause: &[Lit]) {
        self.queue.push(clause.len() as i32);
        for l in clause.iter() {
            self.queue.push(i32::from(*l));
        }
        if DUMP_INTERVAL < self.queue.len() {
            self.dump_to_file();
        }
    }
    #[cfg(feature = "no_IO")]
    pub fn delete_clause(&mut self, _vec: &[Lit]) {}
    #[cfg(not(feature = "no_IO"))]
    pub fn delete_clause(&mut self, clause: &[Lit]) {
        self.queue.push((clause.len() as i32).neg());
        for l in clause.iter() {
            self.queue.push(i32::from(*l));
        }
        if DUMP_INTERVAL < self.queue.len() {
            self.dump_to_file();
        }
    }
    #[cfg(feature = "no_IO")]
    pub fn close(&mut self) {}
    #[cfg(not(feature = "no_IO"))]
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
                for _ in 0..(l.abs() as usize) {
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

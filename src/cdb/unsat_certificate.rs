#[cfg(not(feature = "no_IO"))]
use std::{
    fs::File,
    io::{BufWriter, Write},
    path::PathBuf,
};

use crate::types::*;

#[derive(Debug)]
pub struct CertificationDumper {
    target: Option<PathBuf>,
    buffer: Option<BufWriter<File>>,
}

impl Clone for CertificationDumper {
    fn clone(&self) -> Self {
        Self::default()
    }
}

impl Default for CertificationDumper {
    fn default() -> Self {
        CertificationDumper {
            buffer: None,
            target: None,
        }
    }
}

impl Instantiate for CertificationDumper {
    fn instantiate(config: &Config, _cnf: &CNFDescription) -> Self {
        #[cfg(not(feature = "no_IO"))]
        if config.use_certification {
            let cert: PathBuf = config.io_odir.join(&config.io_pfile);
            if let Ok(out) = File::create(&cert) {
                return CertificationDumper {
                    buffer: Some(BufWriter::new(out)),
                    target: Some(cert),
                };
            }
        }
        CertificationDumper::default()
    }
}

impl CertificationDumper {
    #[cfg(feature = "no_IO")]
    pub fn push_add(&mut self, _vec: &[Lit]) {}
    #[cfg(not(feature = "no_IO"))]
    pub fn push_add(&mut self, vec: &[Lit]) {
        if let Some(ref mut buf) = self.buffer {
            for l in vec {
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
    #[cfg(feature = "no_IO")]
    pub fn push_delete(&mut self, _vec: &[Lit]) {}
    #[cfg(not(feature = "no_IO"))]
    pub fn push_delete(&mut self, vec: &[Lit]) {
        if let Some(ref mut buf) = self.buffer {
            if buf.write_all(b"d ").is_err() {
                self.buffer = None;
                return;
            }
            for l in vec {
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
    #[cfg(feature = "no_IO")]
    pub fn close(&mut self) {}
    #[cfg(not(feature = "no_IO"))]
    pub fn close(&mut self) {
        if let Some(ref mut buf) = self.buffer {
            let _ = buf.write_all(b"0\n");
            self.buffer = None;
            self.target = None;
        }
    }
}

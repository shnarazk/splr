pub struct Histogram {
    pub bands: [usize; 128],
    pub samples: usize,
}

impl Default for Histogram {
    fn default() -> Self {
        Self {
            bands: [0; 128],
            samples: 0,
        }
    }
}

impl Histogram {
    pub fn add(&mut self, d: f64) -> f64 {
        let index = ((128.0 * d) as usize).clamp(0, 127);
        self.bands[index] += 1;
        self.samples += 1;
        if index < 64 {
            let med = (0..index).map(|l| self.bands[l]).sum::<usize>() + self.bands[index] / 2;
            med as f64 / (self.samples as f64)
        } else {
            let med =
                (index + 1..128).map(|l| self.bands[l]).sum::<usize>() + self.bands[index] / 2;
            1.0 - med as f64 / (self.samples as f64)
        }
    }
    pub fn rescale(&mut self, scale: f64) {
        self.samples = 0;
        for d in self.bands.iter_mut() {
            *d = (*d as f64 * scale) as usize;
            self.samples += *d;
        }
    }
}

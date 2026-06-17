//! A deterministic, dependency-free pseudo-random number generator.
//!
//! The standard library does not provide a general-purpose RNG, so this is a
//! small [SplitMix64](https://prng.di.unimi.it/splitmix64.c) generator. It is
//! fully deterministic (the same seed always yields the same sequence), fast,
//! and of high statistical quality, which makes it suitable for reproducible
//! randomization inside the solver.

/// A SplitMix64 pseudo-random number generator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SplitMix64 {
    state: u64,
}

impl Default for SplitMix64 {
    fn default() -> Self {
        SplitMix64::new(0)
    }
}

impl SplitMix64 {
    /// Create a generator from a seed. Any seed (including `0`) is valid.
    pub const fn new(seed: u64) -> Self {
        SplitMix64 { state: seed }
    }
    /// Return the next 64-bit pseudo-random value and advance the state.
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// Return a pseudo-random `f64` in the half-open range `[0.0, 1.0)`.
    pub fn next_f64(&mut self) -> f64 {
        // Use the top 53 bits to fill the mantissa of an f64.
        (self.next_u64() >> 11) as f64 / ((1u64 << 53) as f64)
    }
    /// Return a pseudo-random `usize` in the half-open range `[0, bound)`.
    /// Returns `0` when `bound` is `0`.
    pub fn below(&mut self, bound: usize) -> usize {
        if bound == 0 {
            0
        } else {
            (self.next_u64() % bound as u64) as usize
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deterministic() {
        let mut a = SplitMix64::new(12345);
        let mut b = SplitMix64::new(12345);
        for _ in 0..1000 {
            assert_eq!(a.next_u64(), b.next_u64());
        }
    }

    #[test]
    fn test_distinct_seeds_diverge() {
        let mut a = SplitMix64::new(1);
        let mut b = SplitMix64::new(2);
        assert_ne!(a.next_u64(), b.next_u64());
    }

    #[test]
    fn test_next_f64_in_range() {
        let mut r = SplitMix64::new(42);
        for _ in 0..10_000 {
            let x = r.next_f64();
            assert!((0.0..1.0).contains(&x));
        }
    }

    #[test]
    fn test_below_bound() {
        let mut r = SplitMix64::new(7);
        for _ in 0..10_000 {
            assert!(r.below(10) < 10);
        }
        assert_eq!(r.below(0), 0);
    }
}

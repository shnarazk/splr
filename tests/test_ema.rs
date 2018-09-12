#![allow(dead_code)]
#![allow(unused_macros)]
#![allow(unused_imports)]
extern crate splr;
use splr::types::*;

#[test]
fn test_ema() -> () {
    for l in &[1000.0, 2000.0, 8000.0, 10000.0] { 
        let mut s40 = Ema2::new(1.0, 40.0, *l);
        let mut s50 = Ema2::new(1.0, 50.0, *l);
        let mut s99 = Ema2::new(1.0, 99.0, *l);
        for _ in 0..40 { s40.update(2.0); }
        for _ in 0..50 { s50.update(2.0); }
        for _ in 0..99 { s99.update(2.0); }
        println!("l = {}; EMA 40: fast {} slow {}, rate {}", *l, s40.fast, s40.slow, s40.get());
        println!("l = {}; EMA 50: fast {} slow {}, rate {}", *l, s50.fast, s50.slow, s50.get());
        println!("l = {}; EMA 99: fast {} slow {}, rate {}", *l, s99.fast, s99.slow, s99.get());
    }
}

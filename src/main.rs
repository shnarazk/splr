extern crate splr;
use splr::types::*;

fn main() {
    let x : Lit = int2lit(4);
    println!("Hello, world! L{} -> I{}", x, lit2int(x));
}

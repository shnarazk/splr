extern crate splr;
use splr::clause::*;
use splr::types::*;

fn main() {
    let x: Lit = int2lit(4);
    let null = Clause::null();
    let mut c2: BoxClause = Clause::new(vec![int2lit(-1), int2lit(4)]);
    let mut e = Ema::new(1000);
    for _ in 1..20 {
        e.update(0.2);
    }
    (*c2).activity = e.get();
    println!(
        "Hello, world! L{} -> I{}, {}, {:?}, {}",
        x,
        lit2int(x),
        null,
        [null == null, c2 == c2, null == c2],
        (*c2).activity
    );
}

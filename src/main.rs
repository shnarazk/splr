extern crate splr;
use splr::clause::*;
use splr::types::*;

fn main() {
    let x: Lit = int2lit(4);
    let null = Box::new(CLAUSE0);
    let c2 = ClauseKind::new2(int2lit(-1), int2lit(4));
    let mut e = Ema::new(10);
    for _ in 1..20 {
        e.update(0.2);
    }
    println!(
        "Hello, world! L{} -> I{}, {}, {:?}, {}",
        x,
        lit2int(x),
        null,
        [null == null, c2 == c2, null == c2],
        e.get()
    );
}

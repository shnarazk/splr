extern crate splr;
use splr::types::*;
use splr::clause::ClauseKind::*;

fn main() {
    let x : Lit = int2lit(4);
    let c = NullClause;
    let mut e = new_e(10);
    for _ in 1 .. 20 { e.update_e(0.2); };
    println!("Hello, world! L{} -> I{}, {}, {}", x, lit2int(x),c, e.get_e());
}

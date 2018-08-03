extern crate splr;
use splr::types::*;
use splr::clause::ClauseKind::NullClause;

fn main() {
    let x : Lit = int2lit(4);
    let c = NullClause;
    println!("Hello, world! L{} -> I{}, {}", x, lit2int(x),c);
}

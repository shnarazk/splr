#![allow(dead_code)]
#![allow(unused_imports)]

extern crate combine;
extern crate splr;
use combine::parser::byte::{digit, letter, space};
use combine::{many1, sep_by, Parser};
use splr::clause::*;
use splr::search::*;
use splr::solver::*;
use splr::types::*;

fn to_num(v: Vec<u8>) -> i32 {
    let mut a: i32 = 0;
    for d in v {
        a *= 10;
        a += (d as i32) - 48;
    }
    a
}

fn main() {
    println!("Hello, world!");

    //    let stdin = std::io::stdin();
    //    let stdin = stdin.lock();
    //    let stdin_stream = BufferedStream::new(from_read(stdin), 10);
    //    let stdin_stream = stdin_stream.as_stream();

    let mut pint1 = many1::<Vec<_>, _>(combine::parser::byte::digit());
    let mut pint2 = many1::<Vec<_>, _>(combine::parser::byte::digit()).map(to_num);
    let mut parser =
        many1::<Vec<_>, _>(combine::parser::byte::digit().or(combine::parser::byte::space()));
    //    println!("{:?}", parser.parse(stdin_stream));

    println!("{:?}", pint1.parse(&b"123 333 0"[..]));
    println!("{:?}", pint2.parse(&b"123 333 0"[..]));
    //    println!("{:?}", parser.parse("123 333 0"));
    //    println!("{:?}", parser.parse("123ABC"));
    println!("{:?}", parser.parse(&b"ABC123"[..]));

    let cnf = CNFDescription {
        num_of_variables: 8,
        num_of_clauses: 10,
        pathname: "".to_string(),
    };
    let mut s: Solver = Solver::new(DEFAULT_CONFIGURATION, &cnf);
    let x: Lit = int2lit(4);
    let c1 = Clause::new(vec![int2lit(1), int2lit(2), int2lit(3)]);
    let mut c2 = Clause::new(vec![int2lit(-1), int2lit(4)]);
    let mut e = Ema::new(1000);
    for _ in 1..20 {
        e.update(0.2);
    }
    c2.activity = e.get();
    println!("# Literal: L{} -> I{}", x, x.int());
    println!(
        "# Clause: {}, {:?}, {}",
        c1,
        [c1 == c1, c2 == c2, c1 == c2],
        c2.activity
    );
    s.inject(false, c1);
    s.inject(true, c2);
    println!("# Solver: {:?}", s.watches);
    s.solve();
    println!("nclauses = {}", s.num_clauses());
    s.learnts.pop();
    println!("# End of program");
}

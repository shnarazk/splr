fn main() -> () {
    make(100, 4);
}

fn make(nv: u32, chain: u32) -> () {
    println!("p cnf {}, {}", nv, nv);
    for i in 0..nv - chain + 1 {
        print!("{} ", i + chain);
        for j in 1..chain {
            print!("-{} ", i + chain - j);
        }
        println!("0");
    }
    for i in 1..chain {
        println!("{} 0", i);
    }
}

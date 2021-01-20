use {
    csv,
    std::{collections::HashMap, error::Error, io, process},
};

fn parser() -> Result<HashMap<(usize, usize), usize>, Box<dyn Error>> {
    let mut hash: HashMap<(usize, usize), usize> = HashMap::new();
    // Build the CSV reader and iterate over each record.
    let mut rdr = csv::Reader::from_reader(io::stdin());
    for result in rdr.records() {
        // The iterator yields Result<StringRecord, Error>, so we check the
        // error here.
        let record = result?;
        if let (Ok(x), Ok(y)) = (
            record.get(0).map(|x| x.parse::<f64>()).unwrap(),
            record.get(1).map(|y| y.parse::<usize>()).unwrap(),
        ) {
            *hash.entry((x as usize, y)).or_insert(0) += 1;
            // println!("{:.2}, {:.2}", x, y);
        }
    }
    Ok(hash)
}

fn main() {
    match parser() {
        Ok(h) => {
            let mut hash: HashMap<usize, (usize, f64)> = HashMap::new();
            for ((ema, lbd), count) in h {
                let entry = hash.entry(ema).or_insert((0, 0.0));
                *entry = (entry.0 + count, entry.1 + (lbd * count) as f64);
            }
            let mut keys = hash.keys().map(|k| *k).collect::<Vec<usize>>();
            keys.sort_unstable();
            for i in keys.iter() {
                if let Some(v) = hash.get(i) {
                    println!("{},{:.2}", i, v.1 / (v.0 as f64));
                }
            }
        }
        Err(err) => {
            println!("error running example: {}", err);
            process::exit(1);
        }
    }
}

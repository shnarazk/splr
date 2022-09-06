pub mod cnf;
pub use self::cnf::*;

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn it_works() {
        let build = CNF::from_vec_i32(vec![]);
        assert!(build.is_ok());
        let mut cnf = build.unwrap();
        assert!(cnf.add_clause(vec![1, 3, 2]).is_ok());
        assert_eq!(cnf.num_clauses(), 1);
        assert_eq!(cnf.num_vars(), 3);
        assert!(cnf.add_clause(vec![-1, -4, 3]).is_ok());
        assert_eq!(cnf.num_clauses(), 2);
        assert_eq!(cnf.num_vars(), 4);
        let output = cnf.dump_to_string();
        let mut line = output.lines();
        assert_eq!(line.next(), Some("p cnf 4 2"));
        assert_eq!(line.next(), Some("1 3 2 0"));
        assert_eq!(line.next(), Some("-1 -4 3 0"));
    }
    #[test]
    fn test_load_uf8() {
        let build = CNF::load(Path::new("cnfs/uf8.cnf"));
        dbg!(build.is_ok());
        let cnf = build.unwrap();
        assert_eq!(cnf.num_clauses(), 13);
        assert_eq!(cnf.num_vars(), 8);
    }
    #[test]
    fn test_load_sample() {
        let build = CNF::load(Path::new("cnfs/sample.cnf"));
        dbg!(build.is_ok());
        let cnf = build.unwrap();
        assert_eq!(cnf.num_clauses(), 1065);
        assert_eq!(cnf.num_vars(), 250);
    }
}

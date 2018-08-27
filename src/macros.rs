/// In solver's method, use it like
/// ```ignore
/// cref!(self.cv, cid)
/// ```
#[macro_export]
macro_rules! cref {
    ($cv:expr, $val:expr) => {{
        match (&mut $cv, &$val) {
            (v, cid) => &mut v[cid.to_kind()].clauses[cid.to_index()],
        }
    }};
}

macro_rules! lindex {
    ($c:expr, $val:expr) => {{
        match (&$c, &$val) {
            (c, i) => match i {
                0 => c.lit[0],
                1 => c.lit[1],
                n => c.lits[n -2],
            }
        }
    }};
}

